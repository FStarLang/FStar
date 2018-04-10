open Prims
let (instantiate_both :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___68_6 = env  in
    {
      FStar_TypeChecker_Env.solver = (uu___68_6.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___68_6.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___68_6.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___68_6.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___68_6.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___68_6.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___68_6.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___68_6.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___68_6.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___68_6.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___68_6.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___68_6.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___68_6.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___68_6.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___68_6.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___68_6.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___68_6.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___68_6.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___68_6.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___68_6.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___68_6.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___68_6.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___68_6.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___68_6.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___68_6.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___68_6.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___68_6.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___68_6.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.proof_ns =
        (uu___68_6.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___68_6.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice = (uu___68_6.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___68_6.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___68_6.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___68_6.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___68_6.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___68_6.FStar_TypeChecker_Env.dep_graph)
    }
  
let (no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___69_12 = env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___69_12.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___69_12.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___69_12.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___69_12.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___69_12.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___69_12.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___69_12.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___69_12.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___69_12.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___69_12.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___69_12.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___69_12.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___69_12.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___69_12.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___69_12.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___69_12.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___69_12.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___69_12.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___69_12.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___69_12.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___69_12.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___69_12.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___69_12.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___69_12.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___69_12.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___69_12.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___69_12.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___69_12.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.proof_ns =
        (uu___69_12.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___69_12.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___69_12.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___69_12.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___69_12.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___69_12.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___69_12.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___69_12.FStar_TypeChecker_Env.dep_graph)
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
             let uu____49 =
               let uu____50 = FStar_Syntax_Syntax.as_arg v1  in
               let uu____51 =
                 let uu____54 = FStar_Syntax_Syntax.as_arg tl1  in [uu____54]
                  in
               uu____50 :: uu____51  in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____49
              in
           uu____46 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
  
let (is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___63_63  ->
    match uu___63_63 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____66 -> false
  
let steps :
  'Auu____73 . 'Auu____73 -> FStar_TypeChecker_Normalize.step Prims.list =
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
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun head_opt  ->
    fun env  ->
      fun fvs  ->
        fun kt  ->
          let rec aux try_norm t =
            match fvs with
            | [] -> t
            | uu____138 ->
                let t1 = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t1  in
                let uu____146 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____146 with
                 | FStar_Pervasives_Native.None  -> t1
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail1 uu____157 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____159 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____159
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____161 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____162 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____161 uu____162
                             in
                          let uu____163 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____163
                           in
                        let s =
                          let uu____165 =
                            let uu____166 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____166
                             in
                          FStar_TypeChecker_Util.new_uvar env uu____165  in
                        let uu____175 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s  in
                        match uu____175 with
                        | FStar_Pervasives_Native.Some g ->
                            let uu____179 =
                              FStar_TypeChecker_Rel.force_trivial_guard env g
                               in
                            s
                        | uu____180 -> fail1 ()))
             in
          aux false kt
  
let push_binding :
  'Auu____189 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____189) FStar_Pervasives_Native.tuple2 ->
        FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun b  ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
  
let (maybe_extend_subst :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.binder ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t)
  =
  fun s  ->
    fun b  ->
      fun v1  ->
        let uu____227 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____227
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v1))
          :: s
  
let (set_lcomp_result :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____243  ->
           let uu____244 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Util.set_result_typ uu____244 t)
  
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
                let uu____299 = FStar_Syntax_Syntax.mk_Total t  in
                FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____299
            | FStar_Util.Inr lc -> lc  in
          let t = lc.FStar_Syntax_Syntax.res_typ  in
          let uu____308 =
            let uu____315 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____315 with
            | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                let uu____325 =
                  FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                    t'
                   in
                (match uu____325 with
                 | (e1,lc1) ->
                     let t1 = lc1.FStar_Syntax_Syntax.res_typ  in
                     let uu____341 =
                       FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t'
                        in
                     (match uu____341 with
                      | (e2,g) ->
                          let uu____354 =
                            let uu____355 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____355
                            then
                              let uu____356 =
                                FStar_Syntax_Print.term_to_string t1  in
                              let uu____357 =
                                FStar_Syntax_Print.term_to_string t'  in
                              let uu____358 =
                                FStar_TypeChecker_Rel.guard_to_string env g
                                 in
                              let uu____359 =
                                FStar_TypeChecker_Rel.guard_to_string env
                                  guard
                                 in
                              FStar_Util.print4
                                "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                uu____356 uu____357 uu____358 uu____359
                            else ()  in
                          let msg =
                            let uu____367 =
                              FStar_TypeChecker_Rel.is_trivial g  in
                            if uu____367
                            then FStar_Pervasives_Native.None
                            else
                              FStar_All.pipe_left
                                (fun _0_17  ->
                                   FStar_Pervasives_Native.Some _0_17)
                                (FStar_TypeChecker_Err.subtyping_failed env
                                   t1 t')
                             in
                          let g1 = FStar_TypeChecker_Rel.conj_guard g guard
                             in
                          let uu____389 =
                            FStar_TypeChecker_Util.strengthen_precondition
                              msg env e2 lc1 g1
                             in
                          (match uu____389 with
                           | (lc2,g2) ->
                               let uu____402 = set_lcomp_result lc2 t'  in
                               ((memo_tk e2 t'), uu____402, g2))))
             in
          match uu____308 with | (e1,lc1,g) -> (e1, lc1, g)
  
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
        let uu____439 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____439 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____449 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____449 with
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
        let uu____501 = ec  in
        match uu____501 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____523 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____523
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____525 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____525
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
            let uu____527 =
              match copt with
              | FStar_Pervasives_Native.Some uu____540 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____543 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____545 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____545))
                     in
                  if uu____543
                  then
                    let uu____552 =
                      let uu____555 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____555  in
                    (uu____552, c)
                  else
                    (let uu____559 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____559
                     then
                       let uu____566 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____566)
                     else
                       (let uu____570 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____570
                        then
                          let uu____577 =
                            let uu____580 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____580  in
                          (uu____577, c)
                        else (FStar_Pervasives_Native.None, c)))
               in
            (match uu____527 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1  in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let c3 =
                        let uu____607 = FStar_Syntax_Util.lcomp_of_comp c2
                           in
                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                          env e uu____607
                         in
                      let c4 = FStar_Syntax_Syntax.lcomp_comp c3  in
                      let uu____609 =
                        FStar_TypeChecker_Util.check_comp env e c4 expected_c
                         in
                      (match uu____609 with
                       | (e1,uu____623,g) ->
                           let g1 =
                             let uu____626 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_TypeChecker_Util.label_guard uu____626
                               "could not prove post-condition" g
                              in
                           let uu____627 =
                             let uu____628 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low
                                in
                             if uu____628
                             then
                               let uu____629 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               let uu____630 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1
                                  in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____629 uu____630
                             else ()  in
                           let e2 =
                             FStar_TypeChecker_Util.maybe_lift env e1
                               (FStar_Syntax_Util.comp_effect_name c4)
                               (FStar_Syntax_Util.comp_effect_name expected_c)
                               (FStar_Syntax_Util.comp_result c4)
                              in
                           (e2, expected_c, g1))))
  
let no_logical_guard :
  'Auu____641 'Auu____642 .
    FStar_TypeChecker_Env.env ->
      ('Auu____641,'Auu____642,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____641,'Auu____642,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____664  ->
      match uu____664 with
      | (te,kt,f) ->
          let uu____674 = FStar_TypeChecker_Rel.guard_form f  in
          (match uu____674 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____682 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____687 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____682 uu____687)
  
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____699 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____699 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____703 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____703
  
let rec (get_pat_vars :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun pats  ->
    fun acc  ->
      let pats1 = FStar_Syntax_Util.unmeta pats  in
      let uu____735 = FStar_Syntax_Util.head_and_args pats1  in
      match uu____735 with
      | (head1,args) ->
          let uu____774 =
            let uu____775 = FStar_Syntax_Util.un_uinst head1  in
            uu____775.FStar_Syntax_Syntax.n  in
          (match uu____774 with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid
               ->
               let uu____782 = FStar_List.tl args  in
               get_pat_vars_args uu____782 acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.smtpatOr_lid
               -> get_pat_vars_args args acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               -> get_pat_vars_args args acc
           | uu____791 ->
               let uu____792 = FStar_Syntax_Free.names pats1  in
               FStar_Util.set_union acc uu____792)

and (get_pat_vars_args :
  FStar_Syntax_Syntax.args ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun args  ->
    fun acc  ->
      FStar_List.fold_left
        (fun s  ->
           fun arg  -> get_pat_vars (FStar_Pervasives_Native.fst arg) s) acc
        args

let check_smt_pat :
  'Auu____827 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,'Auu____827) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____864 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____864
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____865;
                  FStar_Syntax_Syntax.effect_name = uu____866;
                  FStar_Syntax_Syntax.result_typ = uu____867;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____871)::[];
                  FStar_Syntax_Syntax.flags = uu____872;_}
                ->
                let pat_vars =
                  let uu____920 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta] env pats
                     in
                  let uu____921 =
                    FStar_Util.new_set FStar_Syntax_Syntax.order_bv  in
                  get_pat_vars uu____920 uu____921  in
                let uu____924 =
                  FStar_All.pipe_right bs
                    (FStar_Util.find_opt
                       (fun uu____951  ->
                          match uu____951 with
                          | (b,uu____957) ->
                              let uu____958 = FStar_Util.set_mem b pat_vars
                                 in
                              Prims.op_Negation uu____958))
                   in
                (match uu____924 with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some (x,uu____964) ->
                     let uu____969 =
                       let uu____974 =
                         let uu____975 = FStar_Syntax_Print.bv_to_string x
                            in
                         FStar_Util.format1
                           "Pattern misses at least one bound variable: %s"
                           uu____975
                          in
                       (FStar_Errors.Warning_PatternMissingBoundVar,
                         uu____974)
                        in
                     FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       uu____969)
            | uu____976 -> failwith "Impossible"
          else ()
  
let (guard_letrecs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp ->
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
              let uu___70_1032 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___70_1032.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___70_1032.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___70_1032.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___70_1032.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___70_1032.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___70_1032.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___70_1032.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___70_1032.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___70_1032.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___70_1032.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___70_1032.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___70_1032.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___70_1032.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___70_1032.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___70_1032.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___70_1032.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___70_1032.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___70_1032.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___70_1032.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.failhard =
                  (uu___70_1032.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___70_1032.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.tc_term =
                  (uu___70_1032.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___70_1032.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___70_1032.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___70_1032.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___70_1032.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___70_1032.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___70_1032.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___70_1032.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___70_1032.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___70_1032.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___70_1032.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___70_1032.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___70_1032.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___70_1032.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___70_1032.FStar_TypeChecker_Env.dep_graph)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              let uu____1049 =
                let uu____1050 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                if uu____1050
                then
                  let uu____1051 =
                    FStar_Syntax_Print.binders_to_string ", " bs  in
                  let uu____1052 = FStar_Syntax_Print.comp_to_string c  in
                  FStar_Util.print2
                    "Building a decreases clause over (%s) and %s\n"
                    uu____1051 uu____1052
                else ()  in
              let filter_types_and_functions bs1 =
                FStar_All.pipe_right bs1
                  (FStar_List.collect
                     (fun uu____1072  ->
                        match uu____1072 with
                        | (b,uu____1080) ->
                            let t =
                              let uu____1082 =
                                FStar_Syntax_Util.unrefine
                                  b.FStar_Syntax_Syntax.sort
                                 in
                              FStar_TypeChecker_Normalize.unfold_whnf env1
                                uu____1082
                               in
                            (match t.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_type uu____1085 -> []
                             | FStar_Syntax_Syntax.Tm_arrow uu____1086 -> []
                             | uu____1099 ->
                                 let uu____1100 =
                                   FStar_Syntax_Syntax.bv_to_name b  in
                                 [uu____1100])))
                 in
              let as_lex_list dec =
                let uu____1106 = FStar_Syntax_Util.head_and_args dec  in
                match uu____1106 with
                | (head1,uu____1122) ->
                    (match head1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.lexcons_lid
                         -> dec
                     | uu____1144 -> mk_lex_list [dec])
                 in
              let cflags = FStar_Syntax_Util.comp_flags c  in
              let uu____1148 =
                FStar_All.pipe_right cflags
                  (FStar_List.tryFind
                     (fun uu___64_1157  ->
                        match uu___64_1157 with
                        | FStar_Syntax_Syntax.DECREASES uu____1158 -> true
                        | uu____1161 -> false))
                 in
              match uu____1148 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                  dec) -> as_lex_list dec
              | uu____1165 ->
                  let xs = FStar_All.pipe_right bs filter_types_and_functions
                     in
                  (match xs with | x::[] -> x | uu____1174 -> mk_lex_list xs)
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____1196 =
              match uu____1196 with
              | (l,t,u_names) ->
                  let uu____1214 =
                    let uu____1215 = FStar_Syntax_Subst.compress t  in
                    uu____1215.FStar_Syntax_Syntax.n  in
                  (match uu____1214 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____1276  ->
                                 match uu____1276 with
                                 | (x,imp) ->
                                     let uu____1287 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____1287
                                     then
                                       let uu____1292 =
                                         let uu____1293 =
                                           let uu____1296 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____1296
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____1293
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____1292, imp)
                                     else (x, imp)))
                          in
                       let uu____1298 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____1298 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____1317 =
                                let uu____1320 =
                                  let uu____1321 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____1322 =
                                    let uu____1325 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____1325]  in
                                  uu____1321 :: uu____1322  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____1320
                                 in
                              uu____1317 FStar_Pervasives_Native.None r  in
                            let uu____1328 = FStar_Util.prefix formals2  in
                            (match uu____1328 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___71_1375 = last1  in
                                   let uu____1376 =
                                     FStar_Syntax_Util.refine last1 precedes1
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___71_1375.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___71_1375.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____1376
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 let uu____1401 =
                                   let uu____1402 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low
                                      in
                                   if uu____1402
                                   then
                                     let uu____1403 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____1404 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____1405 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____1403 uu____1404 uu____1405
                                   else ()  in
                                 (l, t', u_names)))
                   | uu____1409 ->
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
        (let uu___72_2009 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___72_2009.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___72_2009.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___72_2009.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___72_2009.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___72_2009.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___72_2009.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___72_2009.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___72_2009.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___72_2009.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___72_2009.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___72_2009.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___72_2009.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___72_2009.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___72_2009.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___72_2009.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___72_2009.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___72_2009.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___72_2009.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___72_2009.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___72_2009.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___72_2009.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___72_2009.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___72_2009.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___72_2009.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___72_2009.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___72_2009.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___72_2009.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___72_2009.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___72_2009.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___72_2009.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___72_2009.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___72_2009.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___72_2009.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___72_2009.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___72_2009.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___72_2009.FStar_TypeChecker_Env.dep_graph)
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
      let uu____2020 =
        let uu____2021 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
           in
        if uu____2021
        then
          let uu____2022 =
            let uu____2023 = FStar_TypeChecker_Env.get_range env1  in
            FStar_All.pipe_left FStar_Range.string_of_range uu____2023  in
          let uu____2024 = FStar_Syntax_Print.tag_of_term e  in
          FStar_Util.print2 "%s (%s)\n" uu____2022 uu____2024
        else ()  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____2033 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_uinst uu____2064 -> tc_value env1 e
      | FStar_Syntax_Syntax.Tm_uvar uu____2071 -> tc_value env1 e
      | FStar_Syntax_Syntax.Tm_bvar uu____2088 -> tc_value env1 e
      | FStar_Syntax_Syntax.Tm_name uu____2089 -> tc_value env1 e
      | FStar_Syntax_Syntax.Tm_fvar uu____2090 -> tc_value env1 e
      | FStar_Syntax_Syntax.Tm_constant uu____2091 -> tc_value env1 e
      | FStar_Syntax_Syntax.Tm_abs uu____2092 -> tc_value env1 e
      | FStar_Syntax_Syntax.Tm_arrow uu____2109 -> tc_value env1 e
      | FStar_Syntax_Syntax.Tm_refine uu____2122 -> tc_value env1 e
      | FStar_Syntax_Syntax.Tm_type uu____2129 -> tc_value env1 e
      | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
      | FStar_Syntax_Syntax.Tm_quoted
          (uu____2130,{
                        FStar_Syntax_Syntax.qkind =
                          FStar_Syntax_Syntax.Quote_static ;
                        FStar_Syntax_Syntax.antiquotes = aqs;_})
          when
          FStar_List.for_all
            (fun uu____2158  ->
               match uu____2158 with
               | (uu____2167,b,uu____2169) -> Prims.op_Negation b) aqs
          ->
          value_check_expected_typ env1 top
            (FStar_Util.Inl FStar_Syntax_Syntax.t_term)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_quoted uu____2174 ->
          let c =
            FStar_Syntax_Syntax.mk_Comp
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_Tac_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_term;
                FStar_Syntax_Syntax.effect_args = [];
                FStar_Syntax_Syntax.flags =
                  [FStar_Syntax_Syntax.SOMETRIVIAL;
                  FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              }
             in
          let uu____2188 =
            let uu____2195 =
              let uu____2200 = FStar_Syntax_Util.lcomp_of_comp c  in
              FStar_Util.Inr uu____2200  in
            value_check_expected_typ env1 top uu____2195
              FStar_TypeChecker_Rel.trivial_guard
             in
          (match uu____2188 with
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
          let uu____2223 = tc_tot_or_gtot_term env1 e1  in
          (match uu____2223 with
           | (e2,c,g) ->
               let g1 =
                 let uu___73_2240 = g  in
                 {
                   FStar_TypeChecker_Env.guard_f =
                     FStar_TypeChecker_Common.Trivial;
                   FStar_TypeChecker_Env.deferred =
                     (uu___73_2240.FStar_TypeChecker_Env.deferred);
                   FStar_TypeChecker_Env.univ_ineqs =
                     (uu___73_2240.FStar_TypeChecker_Env.univ_ineqs);
                   FStar_TypeChecker_Env.implicits =
                     (uu___73_2240.FStar_TypeChecker_Env.implicits)
                 }  in
               let uu____2241 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_meta
                      (e2,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Meta_smt_pat)))
                   FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                  in
               (uu____2241, c, g1))
      | FStar_Syntax_Syntax.Tm_meta
          (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____2262 = FStar_Syntax_Util.type_u ()  in
          (match uu____2262 with
           | (t,u) ->
               let uu____2275 = tc_check_tot_or_gtot_term env1 e1 t  in
               (match uu____2275 with
                | (e2,c,g) ->
                    let uu____2291 =
                      let uu____2306 =
                        FStar_TypeChecker_Env.clear_expected_typ env1  in
                      match uu____2306 with
                      | (env2,uu____2328) -> tc_pats env2 pats  in
                    (match uu____2291 with
                     | (pats1,g') ->
                         let g'1 =
                           let uu___74_2362 = g'  in
                           {
                             FStar_TypeChecker_Env.guard_f =
                               FStar_TypeChecker_Common.Trivial;
                             FStar_TypeChecker_Env.deferred =
                               (uu___74_2362.FStar_TypeChecker_Env.deferred);
                             FStar_TypeChecker_Env.univ_ineqs =
                               (uu___74_2362.FStar_TypeChecker_Env.univ_ineqs);
                             FStar_TypeChecker_Env.implicits =
                               (uu___74_2362.FStar_TypeChecker_Env.implicits)
                           }  in
                         let uu____2363 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_meta
                                (e2,
                                  (FStar_Syntax_Syntax.Meta_pattern pats1)))
                             FStar_Pervasives_Native.None
                             top.FStar_Syntax_Syntax.pos
                            in
                         let uu____2366 =
                           FStar_TypeChecker_Rel.conj_guard g g'1  in
                         (uu____2363, c, uu____2366))))
      | FStar_Syntax_Syntax.Tm_meta
          (e1,FStar_Syntax_Syntax.Meta_desugared
           (FStar_Syntax_Syntax.Sequence ))
          ->
          let uu____2374 =
            let uu____2375 = FStar_Syntax_Subst.compress e1  in
            uu____2375.FStar_Syntax_Syntax.n  in
          (match uu____2374 with
           | FStar_Syntax_Syntax.Tm_let
               ((uu____2384,{ FStar_Syntax_Syntax.lbname = x;
                              FStar_Syntax_Syntax.lbunivs = uu____2386;
                              FStar_Syntax_Syntax.lbtyp = uu____2387;
                              FStar_Syntax_Syntax.lbeff = uu____2388;
                              FStar_Syntax_Syntax.lbdef = e11;
                              FStar_Syntax_Syntax.lbattrs = uu____2390;
                              FStar_Syntax_Syntax.lbpos = uu____2391;_}::[]),e2)
               ->
               let uu____2419 =
                 let uu____2426 =
                   FStar_TypeChecker_Env.set_expected_typ env1
                     FStar_Syntax_Syntax.t_unit
                    in
                 tc_term uu____2426 e11  in
               (match uu____2419 with
                | (e12,c1,g1) ->
                    let uu____2436 = tc_term env1 e2  in
                    (match uu____2436 with
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
                           let uu____2460 =
                             let uu____2465 =
                               let uu____2466 =
                                 let uu____2479 =
                                   let uu____2486 =
                                     let uu____2489 =
                                       FStar_Syntax_Syntax.mk_lb
                                         (x, [],
                                           (c1.FStar_Syntax_Syntax.eff_name),
                                           FStar_Syntax_Syntax.t_unit, e13,
                                           (e13.FStar_Syntax_Syntax.pos))
                                        in
                                     [uu____2489]  in
                                   (false, uu____2486)  in
                                 (uu____2479, e22)  in
                               FStar_Syntax_Syntax.Tm_let uu____2466  in
                             FStar_Syntax_Syntax.mk uu____2465  in
                           uu____2460 FStar_Pervasives_Native.None
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
                         let uu____2511 =
                           FStar_TypeChecker_Rel.conj_guard g1 g2  in
                         (e5, c, uu____2511)))
           | uu____2514 ->
               let uu____2515 = tc_term env1 e1  in
               (match uu____2515 with
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
          (e1,FStar_Syntax_Syntax.Meta_monadic uu____2537) -> tc_term env1 e1
      | FStar_Syntax_Syntax.Tm_meta
          (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____2549) ->
          tc_term env1 e1
      | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
          let uu____2568 = tc_term env1 e1  in
          (match uu____2568 with
           | (e2,c,g) ->
               let e3 =
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (e2, m))
                   FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                  in
               (e3, c, g))
      | FStar_Syntax_Syntax.Tm_ascribed
          (e1,(FStar_Util.Inr expected_c,topt),uu____2592) ->
          let uu____2639 = FStar_TypeChecker_Env.clear_expected_typ env1  in
          (match uu____2639 with
           | (env0,uu____2653) ->
               let uu____2658 = tc_comp env0 expected_c  in
               (match uu____2658 with
                | (expected_c1,uu____2672,g) ->
                    let t_res = FStar_Syntax_Util.comp_result expected_c1  in
                    let uu____2677 =
                      let uu____2684 =
                        FStar_TypeChecker_Env.set_expected_typ env0 t_res  in
                      tc_term uu____2684 e1  in
                    (match uu____2677 with
                     | (e2,c',g') ->
                         let uu____2694 =
                           let uu____2701 =
                             let uu____2706 =
                               FStar_Syntax_Syntax.lcomp_comp c'  in
                             (e2, uu____2706)  in
                           check_expected_effect env0
                             (FStar_Pervasives_Native.Some expected_c1)
                             uu____2701
                            in
                         (match uu____2694 with
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
                                let uu____2754 =
                                  FStar_TypeChecker_Rel.conj_guard g' g''  in
                                FStar_TypeChecker_Rel.conj_guard g uu____2754
                                 in
                              let f1 =
                                match topt1 with
                                | FStar_Pervasives_Native.None  -> f
                                | FStar_Pervasives_Native.Some tactic ->
                                    FStar_TypeChecker_Rel.map_guard f
                                      (fun f1  ->
                                         let uu____2766 =
                                           FStar_Syntax_Util.mk_squash
                                             FStar_Syntax_Syntax.U_zero f1
                                            in
                                         FStar_TypeChecker_Common.mk_by_tactic
                                           tactic uu____2766)
                                 in
                              let uu____2767 =
                                comp_check_expected_typ env1 e4 lc  in
                              (match uu____2767 with
                               | (e5,c,f2) ->
                                   let final_guard =
                                     FStar_TypeChecker_Rel.conj_guard f1 f2
                                      in
                                   (e5, c, final_guard))))))
      | FStar_Syntax_Syntax.Tm_ascribed
          (e1,(FStar_Util.Inl t,topt),uu____2787) ->
          let uu____2834 = FStar_Syntax_Util.type_u ()  in
          (match uu____2834 with
           | (k,u) ->
               let uu____2847 = tc_check_tot_or_gtot_term env1 t k  in
               (match uu____2847 with
                | (t1,uu____2861,f) ->
                    let uu____2863 =
                      let uu____2870 =
                        FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                      tc_term uu____2870 e1  in
                    (match uu____2863 with
                     | (e2,c,g) ->
                         let uu____2880 =
                           let uu____2885 =
                             FStar_TypeChecker_Env.set_range env1
                               t1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Util.strengthen_precondition
                             (FStar_Pervasives_Native.Some
                                (fun uu____2890  ->
                                   FStar_Util.return_all
                                     FStar_TypeChecker_Err.ill_kinded_type))
                             uu____2885 e2 c f
                            in
                         (match uu____2880 with
                          | (c1,f1) ->
                              let uu____2899 =
                                let uu____2906 =
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
                                comp_check_expected_typ env1 uu____2906 c1
                                 in
                              (match uu____2899 with
                               | (e3,c2,f2) ->
                                   let uu____2946 =
                                     let uu____2947 =
                                       FStar_TypeChecker_Rel.conj_guard g f2
                                        in
                                     FStar_TypeChecker_Rel.conj_guard f1
                                       uu____2947
                                      in
                                   (e3, c2, uu____2946))))))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____2948;
             FStar_Syntax_Syntax.vars = uu____2949;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____3012 = FStar_Syntax_Util.head_and_args top  in
          (match uu____3012 with
           | (unary_op,uu____3034) ->
               let head1 =
                 let uu____3058 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                   FStar_Pervasives_Native.None uu____3058
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
             FStar_Syntax_Syntax.pos = uu____3096;
             FStar_Syntax_Syntax.vars = uu____3097;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____3160 = FStar_Syntax_Util.head_and_args top  in
          (match uu____3160 with
           | (unary_op,uu____3182) ->
               let head1 =
                 let uu____3206 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                   FStar_Pervasives_Native.None uu____3206
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
               (FStar_Const.Const_reflect uu____3244);
             FStar_Syntax_Syntax.pos = uu____3245;
             FStar_Syntax_Syntax.vars = uu____3246;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____3309 = FStar_Syntax_Util.head_and_args top  in
          (match uu____3309 with
           | (unary_op,uu____3331) ->
               let head1 =
                 let uu____3355 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                   FStar_Pervasives_Native.None uu____3355
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
             FStar_Syntax_Syntax.pos = uu____3393;
             FStar_Syntax_Syntax.vars = uu____3394;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____3470 = FStar_Syntax_Util.head_and_args top  in
          (match uu____3470 with
           | (unary_op,uu____3492) ->
               let head1 =
                 let uu____3516 =
                   FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                   FStar_Pervasives_Native.None uu____3516
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
             FStar_Syntax_Syntax.pos = uu____3560;
             FStar_Syntax_Syntax.vars = uu____3561;_},(e1,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____3599 =
            let uu____3606 =
              let uu____3607 = FStar_TypeChecker_Env.clear_expected_typ env1
                 in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3607  in
            tc_term uu____3606 e1  in
          (match uu____3599 with
           | (e2,c,g) ->
               let uu____3631 = FStar_Syntax_Util.head_and_args top  in
               (match uu____3631 with
                | (head1,uu____3653) ->
                    let uu____3674 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app
                           (head1, [(e2, FStar_Pervasives_Native.None)]))
                        FStar_Pervasives_Native.None
                        top.FStar_Syntax_Syntax.pos
                       in
                    let uu____3701 =
                      let uu____3702 =
                        let uu____3705 =
                          FStar_Syntax_Syntax.tabbrev
                            FStar_Parser_Const.range_lid
                           in
                        FStar_Syntax_Syntax.mk_Total uu____3705  in
                      FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                        uu____3702
                       in
                    (uu____3674, uu____3701, g)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____3710;
             FStar_Syntax_Syntax.vars = uu____3711;_},(t,FStar_Pervasives_Native.None
                                                       )::(r,FStar_Pervasives_Native.None
                                                           )::[])
          ->
          let uu____3764 = FStar_Syntax_Util.head_and_args top  in
          (match uu____3764 with
           | (head1,uu____3786) ->
               let env' =
                 let uu____3808 =
                   FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                    in
                 FStar_TypeChecker_Env.set_expected_typ env1 uu____3808  in
               let uu____3809 = tc_term env' r  in
               (match uu____3809 with
                | (er,uu____3823,gr) ->
                    let uu____3825 = tc_term env1 t  in
                    (match uu____3825 with
                     | (t1,tt,gt1) ->
                         let g = FStar_TypeChecker_Rel.conj_guard gr gt1  in
                         let uu____3842 =
                           let uu____3845 =
                             let uu____3848 =
                               let uu____3849 = FStar_Syntax_Syntax.as_arg t1
                                  in
                               let uu____3850 =
                                 let uu____3853 =
                                   FStar_Syntax_Syntax.as_arg r  in
                                 [uu____3853]  in
                               uu____3849 :: uu____3850  in
                             FStar_Syntax_Syntax.mk_Tm_app head1 uu____3848
                              in
                           uu____3845 FStar_Pervasives_Native.None
                             top.FStar_Syntax_Syntax.pos
                            in
                         (uu____3842, tt, g))))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____3858;
             FStar_Syntax_Syntax.vars = uu____3859;_},uu____3860)
          ->
          let uu____3881 =
            let uu____3886 =
              let uu____3887 = FStar_Syntax_Print.term_to_string top  in
              FStar_Util.format1 "Ill-applied constant %s" uu____3887  in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____3886)  in
          FStar_Errors.raise_error uu____3881 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____3894;
             FStar_Syntax_Syntax.vars = uu____3895;_},uu____3896)
          ->
          let uu____3917 =
            let uu____3922 =
              let uu____3923 = FStar_Syntax_Print.term_to_string top  in
              FStar_Util.format1 "Ill-applied constant %s" uu____3923  in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____3922)  in
          FStar_Errors.raise_error uu____3917 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify );
             FStar_Syntax_Syntax.pos = uu____3930;
             FStar_Syntax_Syntax.vars = uu____3931;_},(e1,aqual)::[])
          ->
          let uu____3962 =
            if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ()  in
          let uu____3964 = FStar_TypeChecker_Env.clear_expected_typ env1  in
          (match uu____3964 with
           | (env0,uu____3978) ->
               let uu____3983 = tc_term env0 e1  in
               (match uu____3983 with
                | (e2,c,g) ->
                    let uu____3999 = FStar_Syntax_Util.head_and_args top  in
                    (match uu____3999 with
                     | (reify_op,uu____4021) ->
                         let u_c =
                           let uu____4043 =
                             tc_term env0 c.FStar_Syntax_Syntax.res_typ  in
                           match uu____4043 with
                           | (uu____4050,c',uu____4052) ->
                               let uu____4053 =
                                 let uu____4054 =
                                   FStar_Syntax_Subst.compress
                                     c'.FStar_Syntax_Syntax.res_typ
                                    in
                                 uu____4054.FStar_Syntax_Syntax.n  in
                               (match uu____4053 with
                                | FStar_Syntax_Syntax.Tm_type u -> u
                                | uu____4058 ->
                                    let uu____4059 =
                                      FStar_Syntax_Util.type_u ()  in
                                    (match uu____4059 with
                                     | (t,u) ->
                                         let g_opt =
                                           FStar_TypeChecker_Rel.try_teq true
                                             env1
                                             c'.FStar_Syntax_Syntax.res_typ t
                                            in
                                         let uu____4069 =
                                           match g_opt with
                                           | FStar_Pervasives_Native.Some g'
                                               ->
                                               FStar_TypeChecker_Rel.force_trivial_guard
                                                 env1 g'
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____4071 =
                                                 let uu____4072 =
                                                   FStar_Syntax_Print.lcomp_to_string
                                                     c'
                                                    in
                                                 let uu____4073 =
                                                   FStar_Syntax_Print.term_to_string
                                                     c.FStar_Syntax_Syntax.res_typ
                                                    in
                                                 let uu____4074 =
                                                   FStar_Syntax_Print.term_to_string
                                                     c'.FStar_Syntax_Syntax.res_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                   uu____4072 uu____4073
                                                   uu____4074
                                                  in
                                               failwith uu____4071
                                            in
                                         u))
                            in
                         let repr =
                           let uu____4076 = FStar_Syntax_Syntax.lcomp_comp c
                              in
                           FStar_TypeChecker_Env.reify_comp env1 uu____4076
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
                           let uu____4097 = FStar_Syntax_Syntax.mk_Total repr
                              in
                           FStar_All.pipe_right uu____4097
                             FStar_Syntax_Util.lcomp_of_comp
                            in
                         let uu____4098 = comp_check_expected_typ env1 e3 c1
                            in
                         (match uu____4098 with
                          | (e4,c2,g') ->
                              let uu____4114 =
                                FStar_TypeChecker_Rel.conj_guard g g'  in
                              (e4, c2, uu____4114)))))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reflect l);
             FStar_Syntax_Syntax.pos = uu____4116;
             FStar_Syntax_Syntax.vars = uu____4117;_},(e1,aqual)::[])
          ->
          let uu____4148 =
            if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ()  in
          let no_reflect uu____4160 =
            let uu____4161 =
              let uu____4166 =
                FStar_Util.format1 "Effect %s cannot be reified"
                  l.FStar_Ident.str
                 in
              (FStar_Errors.Fatal_EffectCannotBeReified, uu____4166)  in
            FStar_Errors.raise_error uu____4161 e1.FStar_Syntax_Syntax.pos
             in
          let uu____4173 = FStar_Syntax_Util.head_and_args top  in
          (match uu____4173 with
           | (reflect_op,uu____4195) ->
               let uu____4216 = FStar_TypeChecker_Env.effect_decl_opt env1 l
                  in
               (match uu____4216 with
                | FStar_Pervasives_Native.None  -> no_reflect ()
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    let uu____4249 =
                      let uu____4250 =
                        FStar_All.pipe_right qualifiers
                          FStar_Syntax_Syntax.contains_reflectable
                         in
                      Prims.op_Negation uu____4250  in
                    if uu____4249
                    then no_reflect ()
                    else
                      (let uu____4260 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____4260 with
                       | (env_no_ex,topt) ->
                           let uu____4279 =
                             let u = FStar_TypeChecker_Env.new_u_univ ()  in
                             let repr =
                               FStar_TypeChecker_Env.inst_effect_fun_with 
                                 [u] env1 ed
                                 ([], (ed.FStar_Syntax_Syntax.repr))
                                in
                             let t =
                               let uu____4299 =
                                 let uu____4304 =
                                   let uu____4305 =
                                     let uu____4320 =
                                       let uu____4323 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.tun
                                          in
                                       let uu____4324 =
                                         let uu____4327 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         [uu____4327]  in
                                       uu____4323 :: uu____4324  in
                                     (repr, uu____4320)  in
                                   FStar_Syntax_Syntax.Tm_app uu____4305  in
                                 FStar_Syntax_Syntax.mk uu____4304  in
                               uu____4299 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____4333 =
                               let uu____4340 =
                                 let uu____4341 =
                                   FStar_TypeChecker_Env.clear_expected_typ
                                     env1
                                    in
                                 FStar_All.pipe_right uu____4341
                                   FStar_Pervasives_Native.fst
                                  in
                               tc_tot_or_gtot_term uu____4340 t  in
                             match uu____4333 with
                             | (t1,uu____4369,g) ->
                                 let uu____4371 =
                                   let uu____4372 =
                                     FStar_Syntax_Subst.compress t1  in
                                   uu____4372.FStar_Syntax_Syntax.n  in
                                 (match uu____4371 with
                                  | FStar_Syntax_Syntax.Tm_app
                                      (uu____4387,(res,uu____4389)::(wp,uu____4391)::[])
                                      -> (t1, res, wp, g)
                                  | uu____4434 -> failwith "Impossible")
                              in
                           (match uu____4279 with
                            | (expected_repr_typ,res_typ,wp,g0) ->
                                let uu____4465 =
                                  let uu____4470 =
                                    tc_tot_or_gtot_term env_no_ex e1  in
                                  match uu____4470 with
                                  | (e2,c,g) ->
                                      let uu____4484 =
                                        let uu____4485 =
                                          let uu____4486 =
                                            FStar_Syntax_Util.is_total_lcomp
                                              c
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____4486
                                           in
                                        if uu____4485
                                        then
                                          FStar_TypeChecker_Err.add_errors
                                            env1
                                            [(FStar_Errors.Error_UnexpectedGTotComputation,
                                               "Expected Tot, got a GTot computation",
                                               (e2.FStar_Syntax_Syntax.pos))]
                                        else ()  in
                                      let uu____4500 =
                                        FStar_TypeChecker_Rel.try_teq true
                                          env_no_ex
                                          c.FStar_Syntax_Syntax.res_typ
                                          expected_repr_typ
                                         in
                                      (match uu____4500 with
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____4507 =
                                             let uu____4508 =
                                               let uu____4517 =
                                                 let uu____4524 =
                                                   let uu____4525 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ed.FStar_Syntax_Syntax.repr
                                                      in
                                                   let uu____4526 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   FStar_Util.format2
                                                     "Expected an instance of %s; got %s"
                                                     uu____4525 uu____4526
                                                    in
                                                 (FStar_Errors.Error_UnexpectedInstance,
                                                   uu____4524,
                                                   (e2.FStar_Syntax_Syntax.pos))
                                                  in
                                               [uu____4517]  in
                                             FStar_TypeChecker_Err.add_errors
                                               env1 uu____4508
                                              in
                                           let uu____4539 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g g0
                                              in
                                           (e2, uu____4539)
                                       | FStar_Pervasives_Native.Some g' ->
                                           let uu____4541 =
                                             let uu____4542 =
                                               FStar_TypeChecker_Rel.conj_guard
                                                 g g0
                                                in
                                             FStar_TypeChecker_Rel.conj_guard
                                               g' uu____4542
                                              in
                                           (e2, uu____4541))
                                   in
                                (match uu____4465 with
                                 | (e2,g) ->
                                     let c =
                                       let uu____4552 =
                                         let uu____4553 =
                                           let uu____4554 =
                                             let uu____4555 =
                                               env1.FStar_TypeChecker_Env.universe_of
                                                 env1 res_typ
                                                in
                                             [uu____4555]  in
                                           let uu____4556 =
                                             let uu____4565 =
                                               FStar_Syntax_Syntax.as_arg wp
                                                in
                                             [uu____4565]  in
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               uu____4554;
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               res_typ;
                                             FStar_Syntax_Syntax.effect_args
                                               = uu____4556;
                                             FStar_Syntax_Syntax.flags = []
                                           }  in
                                         FStar_Syntax_Syntax.mk_Comp
                                           uu____4553
                                          in
                                       FStar_All.pipe_right uu____4552
                                         FStar_Syntax_Util.lcomp_of_comp
                                        in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____4585 =
                                       comp_check_expected_typ env1 e3 c  in
                                     (match uu____4585 with
                                      | (e4,c1,g') ->
                                          let uu____4601 =
                                            FStar_TypeChecker_Rel.conj_guard
                                              g' g
                                             in
                                          (e4, c1, uu____4601)))))))
      | FStar_Syntax_Syntax.Tm_app (head1,args) when
          FStar_Syntax_Util.is_synth_by_tactic head1 ->
          tc_synth env1 args top.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let env0 = env1  in
          let env2 =
            let uu____4648 =
              let uu____4649 = FStar_TypeChecker_Env.clear_expected_typ env1
                 in
              FStar_All.pipe_right uu____4649 FStar_Pervasives_Native.fst  in
            FStar_All.pipe_right uu____4648 instantiate_both  in
          let uu____4664 =
            let uu____4665 =
              FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
            if uu____4665
            then
              let uu____4666 =
                FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
              let uu____4667 = FStar_Syntax_Print.term_to_string top  in
              FStar_Util.print2 "(%s) Checking app %s\n" uu____4666
                uu____4667
            else ()  in
          let uu____4669 = tc_term (no_inst env2) head1  in
          (match uu____4669 with
           | (head2,chead,g_head) ->
               let uu____4685 =
                 let uu____4692 =
                   ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                      (let uu____4694 = FStar_Options.lax ()  in
                       Prims.op_Negation uu____4694))
                     && (FStar_TypeChecker_Util.short_circuit_head head2)
                    in
                 if uu____4692
                 then
                   let uu____4701 =
                     let uu____4708 = FStar_TypeChecker_Env.expected_typ env0
                        in
                     check_short_circuit_args env2 head2 chead g_head args
                       uu____4708
                      in
                   match uu____4701 with | (e1,c,g) -> (e1, c, g)
                 else
                   (let uu____4721 = FStar_TypeChecker_Env.expected_typ env0
                       in
                    check_application_args env2 head2 chead g_head args
                      uu____4721)
                  in
               (match uu____4685 with
                | (e1,c,g) ->
                    let uu____4733 =
                      let uu____4734 =
                        FStar_TypeChecker_Env.debug env2
                          FStar_Options.Extreme
                         in
                      if uu____4734
                      then
                        let uu____4735 =
                          FStar_TypeChecker_Rel.print_pending_implicits g  in
                        FStar_Util.print1
                          "Introduced {%s} implicits in application\n"
                          uu____4735
                      else ()  in
                    let uu____4737 = comp_check_expected_typ env0 e1 c  in
                    (match uu____4737 with
                     | (e2,c1,g') ->
                         let gimp =
                           let uu____4754 =
                             let uu____4755 =
                               FStar_Syntax_Subst.compress head2  in
                             uu____4755.FStar_Syntax_Syntax.n  in
                           match uu____4754 with
                           | FStar_Syntax_Syntax.Tm_uvar (u,uu____4759) ->
                               let imp =
                                 ("head of application is a uvar", env0, u,
                                   e2, (c1.FStar_Syntax_Syntax.res_typ),
                                   (head2.FStar_Syntax_Syntax.pos))
                                  in
                               let uu___75_4821 =
                                 FStar_TypeChecker_Rel.trivial_guard  in
                               {
                                 FStar_TypeChecker_Env.guard_f =
                                   (uu___75_4821.FStar_TypeChecker_Env.guard_f);
                                 FStar_TypeChecker_Env.deferred =
                                   (uu___75_4821.FStar_TypeChecker_Env.deferred);
                                 FStar_TypeChecker_Env.univ_ineqs =
                                   (uu___75_4821.FStar_TypeChecker_Env.univ_ineqs);
                                 FStar_TypeChecker_Env.implicits = [imp]
                               }
                           | uu____4870 ->
                               FStar_TypeChecker_Rel.trivial_guard
                            in
                         let gres =
                           let uu____4872 =
                             FStar_TypeChecker_Rel.conj_guard g' gimp  in
                           FStar_TypeChecker_Rel.conj_guard g uu____4872  in
                         let uu____4873 =
                           let uu____4874 =
                             FStar_TypeChecker_Env.debug env2
                               FStar_Options.Extreme
                              in
                           if uu____4874
                           then
                             let uu____4875 =
                               FStar_Syntax_Print.term_to_string e2  in
                             let uu____4876 =
                               FStar_TypeChecker_Rel.guard_to_string env2
                                 gres
                                in
                             FStar_Util.print2
                               "Guard from application node %s is %s\n"
                               uu____4875 uu____4876
                           else ()  in
                         (e2, c1, gres))))
      | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
          let uu____4916 = FStar_TypeChecker_Env.clear_expected_typ env1  in
          (match uu____4916 with
           | (env11,topt) ->
               let env12 = instantiate_both env11  in
               let uu____4936 = tc_term env12 e1  in
               (match uu____4936 with
                | (e11,c1,g1) ->
                    let uu____4952 =
                      match topt with
                      | FStar_Pervasives_Native.Some t -> (env1, t)
                      | FStar_Pervasives_Native.None  ->
                          let uu____4962 = FStar_Syntax_Util.type_u ()  in
                          (match uu____4962 with
                           | (k,uu____4972) ->
                               let res_t =
                                 FStar_TypeChecker_Util.new_uvar env1 k  in
                               let uu____4974 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   res_t
                                  in
                               (uu____4974, res_t))
                       in
                    (match uu____4952 with
                     | (env_branches,res_t) ->
                         let uu____4983 =
                           let uu____4984 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Extreme
                              in
                           if uu____4984
                           then
                             let uu____4985 =
                               FStar_Syntax_Print.term_to_string res_t  in
                             FStar_Util.print1
                               "Tm_match: expected type of branches is %s\n"
                               uu____4985
                           else ()  in
                         let guard_x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (e11.FStar_Syntax_Syntax.pos))
                             c1.FStar_Syntax_Syntax.res_typ
                            in
                         let t_eqns =
                           FStar_All.pipe_right eqns
                             (FStar_List.map (tc_eqn guard_x env_branches))
                            in
                         let uu____5098 =
                           let uu____5103 =
                             FStar_List.fold_right
                               (fun uu____5178  ->
                                  fun uu____5179  ->
                                    match (uu____5178, uu____5179) with
                                    | ((branch1,f,eff_label,cflags,c,g),
                                       (caccum,gaccum)) ->
                                        let uu____5393 =
                                          FStar_TypeChecker_Rel.conj_guard g
                                            gaccum
                                           in
                                        (((f, eff_label, cflags, c) ::
                                          caccum), uu____5393)) t_eqns
                               ([], FStar_TypeChecker_Rel.trivial_guard)
                              in
                           match uu____5103 with
                           | (cases,g) ->
                               let uu____5491 =
                                 FStar_TypeChecker_Util.bind_cases env1 res_t
                                   cases
                                  in
                               (uu____5491, g)
                            in
                         (match uu____5098 with
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
                                         (fun uu____5608  ->
                                            match uu____5608 with
                                            | ((pat,wopt,br),uu____5644,eff_label,uu____5646,uu____5647,uu____5648)
                                                ->
                                                let uu____5671 =
                                                  FStar_TypeChecker_Util.maybe_lift
                                                    env1 br eff_label
                                                    cres.FStar_Syntax_Syntax.eff_name
                                                    res_t
                                                   in
                                                (pat, wopt, uu____5671)))
                                     in
                                  let e2 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_match
                                         (scrutinee, branches))
                                      FStar_Pervasives_Native.None
                                      top.FStar_Syntax_Syntax.pos
                                     in
                                  let e3 =
                                    FStar_TypeChecker_Util.maybe_monadic env1
                                      e2 cres.FStar_Syntax_Syntax.eff_name
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
                                let uu____5726 =
                                  FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                    env1 c1.FStar_Syntax_Syntax.eff_name
                                   in
                                if uu____5726
                                then mk_match e11
                                else
                                  (let e_match =
                                     let uu____5733 =
                                       FStar_Syntax_Syntax.bv_to_name guard_x
                                        in
                                     mk_match uu____5733  in
                                   let lb =
                                     let uu____5737 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         env1 c1.FStar_Syntax_Syntax.eff_name
                                        in
                                     FStar_Syntax_Util.mk_letbinding
                                       (FStar_Util.Inl guard_x) []
                                       c1.FStar_Syntax_Syntax.res_typ
                                       uu____5737 e11 []
                                       e11.FStar_Syntax_Syntax.pos
                                      in
                                   let e2 =
                                     let uu____5743 =
                                       let uu____5748 =
                                         let uu____5749 =
                                           let uu____5762 =
                                             let uu____5763 =
                                               let uu____5764 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   guard_x
                                                  in
                                               [uu____5764]  in
                                             FStar_Syntax_Subst.close
                                               uu____5763 e_match
                                              in
                                           ((false, [lb]), uu____5762)  in
                                         FStar_Syntax_Syntax.Tm_let
                                           uu____5749
                                          in
                                       FStar_Syntax_Syntax.mk uu____5748  in
                                     uu____5743 FStar_Pervasives_Native.None
                                       top.FStar_Syntax_Syntax.pos
                                      in
                                   FStar_TypeChecker_Util.maybe_monadic env1
                                     e2 cres.FStar_Syntax_Syntax.eff_name
                                     cres.FStar_Syntax_Syntax.res_typ)
                                 in
                              let uu____5776 =
                                let uu____5777 =
                                  FStar_TypeChecker_Env.debug env1
                                    FStar_Options.Extreme
                                   in
                                if uu____5777
                                then
                                  let uu____5778 =
                                    FStar_Range.string_of_range
                                      top.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____5779 =
                                    FStar_Syntax_Print.lcomp_to_string cres
                                     in
                                  FStar_Util.print2 "(%s) comp type = %s\n"
                                    uu____5778 uu____5779
                                else ()  in
                              let uu____5781 =
                                FStar_TypeChecker_Rel.conj_guard g1
                                  g_branches
                                 in
                              (e2, cres, uu____5781)))))
      | FStar_Syntax_Syntax.Tm_let
          ((false
            ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5784;
               FStar_Syntax_Syntax.lbunivs = uu____5785;
               FStar_Syntax_Syntax.lbtyp = uu____5786;
               FStar_Syntax_Syntax.lbeff = uu____5787;
               FStar_Syntax_Syntax.lbdef = uu____5788;
               FStar_Syntax_Syntax.lbattrs = uu____5789;
               FStar_Syntax_Syntax.lbpos = uu____5790;_}::[]),uu____5791)
          -> check_top_level_let env1 top
      | FStar_Syntax_Syntax.Tm_let ((false ,uu____5814),uu____5815) ->
          check_inner_let env1 top
      | FStar_Syntax_Syntax.Tm_let
          ((true
            ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5830;
               FStar_Syntax_Syntax.lbunivs = uu____5831;
               FStar_Syntax_Syntax.lbtyp = uu____5832;
               FStar_Syntax_Syntax.lbeff = uu____5833;
               FStar_Syntax_Syntax.lbdef = uu____5834;
               FStar_Syntax_Syntax.lbattrs = uu____5835;
               FStar_Syntax_Syntax.lbpos = uu____5836;_}::uu____5837),uu____5838)
          -> check_top_level_let_rec env1 top
      | FStar_Syntax_Syntax.Tm_let ((true ,uu____5863),uu____5864) ->
          check_inner_let_rec env1 top

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
        let uu____5890 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5980))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____6039 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_SynthByTacticError,
                  "synth_by_tactic: bad application") rng
           in
        match uu____5890 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____6123 = FStar_TypeChecker_Env.expected_typ env  in
                  (match uu____6123 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____6129 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_SynthByTacticError,
                           "synth_by_tactic: need a type annotation when no expected type is present")
                         uu____6129)
               in
            let uu____6132 = FStar_TypeChecker_Env.clear_expected_typ env  in
            (match uu____6132 with
             | (env',uu____6146) ->
                 let uu____6151 = tc_term env' typ  in
                 (match uu____6151 with
                  | (typ1,uu____6165,g1) ->
                      let uu____6167 =
                        FStar_TypeChecker_Rel.force_trivial_guard env' g1  in
                      let uu____6168 = tc_tactic env' tau  in
                      (match uu____6168 with
                       | (tau1,uu____6182,g2) ->
                           let uu____6184 =
                             FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2
                              in
                           let t =
                             if env.FStar_TypeChecker_Env.nosynth
                             then
                               let uu____6190 =
                                 let uu____6193 =
                                   FStar_TypeChecker_Util.fvar_const env
                                     FStar_Parser_Const.magic_lid
                                    in
                                 let uu____6194 =
                                   let uu____6195 =
                                     FStar_Syntax_Syntax.as_arg
                                       FStar_Syntax_Util.exp_unit
                                      in
                                   [uu____6195]  in
                                 FStar_Syntax_Syntax.mk_Tm_app uu____6193
                                   uu____6194
                                  in
                               uu____6190 FStar_Pervasives_Native.None rng
                             else
                               (let t =
                                  env.FStar_TypeChecker_Env.synth_hook env'
                                    typ1 tau1
                                   in
                                let uu____6200 =
                                  let uu____6201 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Tac")
                                     in
                                  if uu____6201
                                  then
                                    let uu____6202 =
                                      FStar_Syntax_Print.term_to_string t  in
                                    FStar_Util.print1 "Got %s\n" uu____6202
                                  else ()  in
                                t)
                              in
                           let uu____6204 =
                             FStar_TypeChecker_Util.check_uvars
                               tau1.FStar_Syntax_Syntax.pos t
                              in
                           let uu____6205 =
                             FStar_Syntax_Syntax.mk_Tm_app t rest
                               FStar_Pervasives_Native.None rng
                              in
                           tc_term env uu____6205)))

and (tc_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___76_6209 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___76_6209.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___76_6209.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___76_6209.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___76_6209.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___76_6209.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___76_6209.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___76_6209.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___76_6209.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___76_6209.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___76_6209.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___76_6209.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___76_6209.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___76_6209.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___76_6209.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___76_6209.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___76_6209.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___76_6209.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___76_6209.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___76_6209.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___76_6209.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___76_6209.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___76_6209.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___76_6209.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___76_6209.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___76_6209.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___76_6209.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___76_6209.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___76_6209.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___76_6209.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___76_6209.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___76_6209.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___76_6209.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___76_6209.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___76_6209.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___76_6209.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___76_6209.FStar_TypeChecker_Env.dep_graph)
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
        let uu___77_6213 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___77_6213.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___77_6213.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___77_6213.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___77_6213.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___77_6213.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___77_6213.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___77_6213.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___77_6213.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___77_6213.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___77_6213.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___77_6213.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___77_6213.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___77_6213.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___77_6213.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___77_6213.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___77_6213.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___77_6213.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___77_6213.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___77_6213.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___77_6213.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___77_6213.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___77_6213.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___77_6213.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___77_6213.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___77_6213.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___77_6213.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___77_6213.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___77_6213.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___77_6213.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___77_6213.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___77_6213.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___77_6213.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___77_6213.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___77_6213.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___77_6213.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___77_6213.FStar_TypeChecker_Env.dep_graph)
        }  in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tac_unit

and (tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun topt  ->
      match topt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some tactic ->
          let uu____6233 = tc_tactic env tactic  in
          (match uu____6233 with
           | (tactic1,uu____6245,uu____6246) ->
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
        let uu____6290 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____6290 with
        | (e2,t,implicits) ->
            let tc =
              let uu____6311 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____6311
              then FStar_Util.Inl t
              else
                (let uu____6317 =
                   let uu____6318 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____6318
                    in
                 FStar_Util.Inr uu____6317)
               in
            let is_data_ctor uu___65_6329 =
              match uu___65_6329 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____6332) -> true
              | uu____6339 -> false  in
            let uu____6342 =
              (is_data_ctor dc) &&
                (let uu____6344 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____6344)
               in
            if uu____6342
            then
              let uu____6351 =
                let uu____6356 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____6356)  in
              let uu____6357 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____6351 uu____6357
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____6374 =
            let uu____6375 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____6375
             in
          failwith uu____6374
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____6409 =
              let uu____6410 = FStar_Syntax_Subst.compress t1  in
              uu____6410.FStar_Syntax_Syntax.n  in
            match uu____6409 with
            | FStar_Syntax_Syntax.Tm_arrow uu____6413 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____6426 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos))
                   in
                let uu___78_6464 = FStar_TypeChecker_Rel.trivial_guard  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___78_6464.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___78_6464.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___78_6464.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                }
             in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____6516 =
            let uu____6529 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____6529 with
            | FStar_Pervasives_Native.None  ->
                let uu____6544 = FStar_Syntax_Util.type_u ()  in
                (match uu____6544 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard)
             in
          (match uu____6516 with
           | (t,uu____6581,g0) ->
               let uu____6595 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____6595 with
                | (e1,uu____6615,g1) ->
                    let uu____6629 =
                      let uu____6630 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____6630
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____6631 = FStar_TypeChecker_Rel.conj_guard g0 g1
                       in
                    (e1, uu____6629, uu____6631)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____6633 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____6646 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____6646)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____6633 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___79_6665 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___79_6665.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___79_6665.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               let uu____6666 =
                 FStar_TypeChecker_Env.insert_bv_info env1 x1 t  in
               let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
               let uu____6668 =
                 FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
               (match uu____6668 with
                | (e2,t1,implicits) ->
                    let tc =
                      let uu____6689 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____6689
                      then FStar_Util.Inl t1
                      else
                        (let uu____6695 =
                           let uu____6696 = FStar_Syntax_Syntax.mk_Total t1
                              in
                           FStar_All.pipe_left
                             FStar_Syntax_Util.lcomp_of_comp uu____6696
                            in
                         FStar_Util.Inr uu____6695)
                       in
                    value_check_expected_typ env1 e2 tc implicits))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6702;
             FStar_Syntax_Syntax.vars = uu____6703;_},uu____6704)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____6709 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____6709
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____6717 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____6717
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6725;
             FStar_Syntax_Syntax.vars = uu____6726;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____6735 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6735 with
           | ((us',t),range) ->
               let uu____6757 =
                 if (FStar_List.length us1) <> (FStar_List.length us')
                 then
                   let uu____6758 =
                     let uu____6763 =
                       let uu____6764 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____6765 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____6766 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____6764 uu____6765 uu____6766
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____6763)
                      in
                   let uu____6767 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____6758 uu____6767
                 else
                   FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____6783 -> failwith "Impossible") us' us1
                  in
               let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
               let uu____6785 =
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t  in
               let e1 =
                 let uu____6787 =
                   FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv')
                     FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____6787 us1  in
               check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name
                 fv'.FStar_Syntax_Syntax.fv_qual e1 t)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6789 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6789 with
           | ((us,t),range) ->
               let uu____6811 =
                 let uu____6812 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____6812
                 then
                   let uu____6813 =
                     let uu____6814 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____6814  in
                   let uu____6815 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____6816 = FStar_Range.string_of_range range  in
                   let uu____6817 = FStar_Range.string_of_use_range range  in
                   let uu____6818 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____6813 uu____6815 uu____6816 uu____6817 uu____6818
                 else ()  in
               let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
               let uu____6821 =
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t  in
               let e1 =
                 let uu____6823 =
                   FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv')
                     FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____6823 us  in
               check_instantiated_fvar env1 fv'.FStar_Syntax_Syntax.fv_name
                 fv'.FStar_Syntax_Syntax.fv_qual e1 t)
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant env1 top.FStar_Syntax_Syntax.pos c  in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6847 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6847 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____6861 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____6861 with
                | (env2,uu____6875) ->
                    let uu____6880 = tc_binders env2 bs1  in
                    (match uu____6880 with
                     | (bs2,env3,g,us) ->
                         let uu____6899 = tc_comp env3 c1  in
                         (match uu____6899 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___80_6918 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___80_6918.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___80_6918.FStar_Syntax_Syntax.vars)
                                }  in
                              let uu____6921 = check_smt_pat env3 e1 bs2 c2
                                 in
                              let u = FStar_Syntax_Syntax.U_max (uc :: us)
                                 in
                              let t =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_type u)
                                  FStar_Pervasives_Native.None
                                  top.FStar_Syntax_Syntax.pos
                                 in
                              let g1 =
                                let uu____6927 =
                                  FStar_TypeChecker_Rel.close_guard_univs us
                                    bs2 f
                                   in
                                FStar_TypeChecker_Rel.conj_guard g uu____6927
                                 in
                              value_check_expected_typ env0 e1
                                (FStar_Util.Inl t) g1))))
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
          let uu____6946 =
            let uu____6951 =
              let uu____6952 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____6952]  in
            FStar_Syntax_Subst.open_term uu____6951 phi  in
          (match uu____6946 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____6962 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____6962 with
                | (env2,uu____6976) ->
                    let uu____6981 =
                      let uu____6994 = FStar_List.hd x1  in
                      tc_binder env2 uu____6994  in
                    (match uu____6981 with
                     | (x2,env3,f1,u) ->
                         let uu____7021 =
                           let uu____7022 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____7022
                           then
                             let uu____7023 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____7024 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____7025 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____7023 uu____7024 uu____7025
                           else ()  in
                         let uu____7027 = FStar_Syntax_Util.type_u ()  in
                         (match uu____7027 with
                          | (t_phi,uu____7039) ->
                              let uu____7040 =
                                tc_check_tot_or_gtot_term env3 phi1 t_phi  in
                              (match uu____7040 with
                               | (phi2,uu____7054,f2) ->
                                   let e1 =
                                     let uu___81_7059 =
                                       FStar_Syntax_Util.refine
                                         (FStar_Pervasives_Native.fst x2)
                                         phi2
                                        in
                                     {
                                       FStar_Syntax_Syntax.n =
                                         (uu___81_7059.FStar_Syntax_Syntax.n);
                                       FStar_Syntax_Syntax.pos =
                                         (top.FStar_Syntax_Syntax.pos);
                                       FStar_Syntax_Syntax.vars =
                                         (uu___81_7059.FStar_Syntax_Syntax.vars)
                                     }  in
                                   let t =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_type u)
                                       FStar_Pervasives_Native.None
                                       top.FStar_Syntax_Syntax.pos
                                      in
                                   let g =
                                     let uu____7066 =
                                       FStar_TypeChecker_Rel.close_guard_univs
                                         [u] [x2] f2
                                        in
                                     FStar_TypeChecker_Rel.conj_guard f1
                                       uu____7066
                                      in
                                   value_check_expected_typ env0 e1
                                     (FStar_Util.Inl t) g)))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____7079) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          let uu____7101 =
            let uu____7102 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
            if uu____7102
            then
              let uu____7103 =
                FStar_Syntax_Print.term_to_string
                  (let uu___82_7106 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___82_7106.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___82_7106.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____7103
            else ()  in
          let uu____7112 = FStar_Syntax_Subst.open_term bs1 body  in
          (match uu____7112 with | (bs2,body1) -> tc_abs env1 top bs2 body1)
      | uu____7125 ->
          let uu____7126 =
            let uu____7127 = FStar_Syntax_Print.term_to_string top  in
            let uu____7128 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____7127
              uu____7128
             in
          failwith uu____7126

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____7138 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____7139,FStar_Pervasives_Native.None ) ->
            FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____7150,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____7166 -> FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_float uu____7171 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____7172 ->
            let uu____7173 =
              let uu____7178 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
                 in
              FStar_All.pipe_right uu____7178 FStar_Util.must  in
            FStar_All.pipe_right uu____7173 FStar_Pervasives_Native.fst
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____7203 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____7204 =
              let uu____7209 =
                let uu____7210 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7210
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7209)  in
            FStar_Errors.raise_error uu____7204 r
        | FStar_Const.Const_set_range_of  ->
            let uu____7211 =
              let uu____7216 =
                let uu____7217 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7217
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7216)  in
            FStar_Errors.raise_error uu____7211 r
        | FStar_Const.Const_reify  ->
            let uu____7218 =
              let uu____7223 =
                let uu____7224 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7224
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7223)  in
            FStar_Errors.raise_error uu____7218 r
        | FStar_Const.Const_reflect uu____7225 ->
            let uu____7226 =
              let uu____7231 =
                let uu____7232 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7232
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7231)  in
            FStar_Errors.raise_error uu____7226 r
        | uu____7233 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____7250) ->
          let uu____7259 = FStar_Syntax_Util.type_u ()  in
          (match uu____7259 with
           | (k,u) ->
               let uu____7272 = tc_check_tot_or_gtot_term env t k  in
               (match uu____7272 with
                | (t1,uu____7286,g) ->
                    let uu____7288 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____7288, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____7290) ->
          let uu____7299 = FStar_Syntax_Util.type_u ()  in
          (match uu____7299 with
           | (k,u) ->
               let uu____7312 = tc_check_tot_or_gtot_term env t k  in
               (match uu____7312 with
                | (t1,uu____7326,g) ->
                    let uu____7328 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____7328, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head1 =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
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
            let uu____7336 =
              let uu____7339 =
                let uu____7340 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____7340 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____7339  in
            uu____7336 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____7343 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____7343 with
           | (tc1,uu____7357,f) ->
               let uu____7359 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____7359 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____7403 =
                        let uu____7404 = FStar_Syntax_Subst.compress head3
                           in
                        uu____7404.FStar_Syntax_Syntax.n  in
                      match uu____7403 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____7407,us) -> us
                      | uu____7413 -> []  in
                    let uu____7414 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____7414 with
                     | (uu____7435,args1) ->
                         let uu____7457 =
                           let uu____7476 = FStar_List.hd args1  in
                           let uu____7489 = FStar_List.tl args1  in
                           (uu____7476, uu____7489)  in
                         (match uu____7457 with
                          | (res,args2) ->
                              let uu____7554 =
                                let uu____7563 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___66_7591  ->
                                          match uu___66_7591 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____7599 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____7599 with
                                               | (env1,uu____7611) ->
                                                   let uu____7616 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____7616 with
                                                    | (e1,uu____7628,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____7563
                                  FStar_List.unzip
                                 in
                              (match uu____7554 with
                               | (flags1,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___83_7667 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___83_7667.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___83_7667.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____7671 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u
                                        in
                                     match uu____7671 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let uu____7675 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____7675))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____7684 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____7685 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____7695 = aux u3  in FStar_Syntax_Syntax.U_succ uu____7695
        | FStar_Syntax_Syntax.U_max us ->
            let uu____7699 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____7699
        | FStar_Syntax_Syntax.U_name x ->
            let uu____7703 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____7703
            then u2
            else
              (let uu____7705 =
                 let uu____7706 =
                   let uu____7707 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.strcat uu____7707 " not found"  in
                 Prims.strcat "Universe variable " uu____7706  in
               failwith uu____7705)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____7709 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____7709 FStar_Pervasives_Native.snd
         | uu____7718 -> aux u)

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
          let fail1 a msg t =
            let uu____7742 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____7742 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____7842 bs2 bs_expected1 =
              match uu____7842 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       let uu____8009 =
                         match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____8010)) ->
                             let uu____8015 =
                               let uu____8020 =
                                 let uu____8021 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____8021
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____8020)
                                in
                             let uu____8022 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____8015 uu____8022
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____8023),FStar_Pervasives_Native.None ) ->
                             let uu____8028 =
                               let uu____8033 =
                                 let uu____8034 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____8034
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____8033)
                                in
                             let uu____8035 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____8028 uu____8035
                         | uu____8036 -> ()  in
                       let expected_t =
                         FStar_Syntax_Subst.subst subst1
                           hd_expected.FStar_Syntax_Syntax.sort
                          in
                       let uu____8042 =
                         let uu____8047 =
                           let uu____8048 =
                             FStar_Syntax_Util.unmeta
                               hd1.FStar_Syntax_Syntax.sort
                              in
                           uu____8048.FStar_Syntax_Syntax.n  in
                         match uu____8047 with
                         | FStar_Syntax_Syntax.Tm_unknown  -> (expected_t, g)
                         | uu____8055 ->
                             let uu____8056 =
                               let uu____8057 =
                                 FStar_TypeChecker_Env.debug env2
                                   FStar_Options.High
                                  in
                               if uu____8057
                               then
                                 let uu____8058 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.print1 "Checking binder %s\n"
                                   uu____8058
                               else ()  in
                             let uu____8060 =
                               tc_tot_or_gtot_term env2
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             (match uu____8060 with
                              | (t,uu____8072,g1) ->
                                  let g2 =
                                    let uu____8075 =
                                      FStar_TypeChecker_Rel.teq_nosmt env2 t
                                        expected_t
                                       in
                                    if uu____8075
                                    then FStar_TypeChecker_Rel.trivial_guard
                                    else
                                      (let uu____8077 =
                                         FStar_TypeChecker_Rel.get_subtyping_prop
                                           env2 expected_t t
                                          in
                                       match uu____8077 with
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8080 =
                                             FStar_TypeChecker_Err.basic_type_error
                                               env2
                                               FStar_Pervasives_Native.None
                                               expected_t t
                                              in
                                           let uu____8085 =
                                             FStar_TypeChecker_Env.get_range
                                               env2
                                              in
                                           FStar_Errors.raise_error
                                             uu____8080 uu____8085
                                       | FStar_Pervasives_Native.Some g2 ->
                                           let uu____8087 =
                                             FStar_TypeChecker_Env.get_range
                                               env2
                                              in
                                           FStar_TypeChecker_Util.label_guard
                                             uu____8087
                                             "Type annotation on parameter incompatible with the expected type"
                                             g2)
                                     in
                                  let g3 =
                                    let uu____8089 =
                                      FStar_TypeChecker_Rel.conj_guard g1 g2
                                       in
                                    FStar_TypeChecker_Rel.conj_guard g
                                      uu____8089
                                     in
                                  (t, g3))
                          in
                       (match uu____8042 with
                        | (t,g1) ->
                            let hd2 =
                              let uu___84_8117 = hd1  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___84_8117.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___84_8117.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }  in
                            let b = (hd2, imp)  in
                            let b_expected = (hd_expected, imp')  in
                            let env3 = push_binding env2 b  in
                            let subst2 =
                              let uu____8130 =
                                FStar_Syntax_Syntax.bv_to_name hd2  in
                              maybe_extend_subst subst1 b_expected uu____8130
                               in
                            aux (env3, (b :: out), g1, subst2) bs3
                              bs_expected2)
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
                let uu____8274 =
                  match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____8281 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type"
                   in
                let uu____8290 = tc_binders env1 bs  in
                (match uu____8290 with
                 | (bs1,envbody,g,uu____8320) ->
                     (FStar_Pervasives_Native.None, bs1, [],
                       FStar_Pervasives_Native.None, envbody, body1, g))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____8366 =
                    let uu____8367 = FStar_Syntax_Subst.compress t2  in
                    uu____8367.FStar_Syntax_Syntax.n  in
                  match uu____8366 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____8390 ->
                      let uu____8407 =
                        match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8414 -> failwith "Impossible"  in
                      let uu____8423 = tc_binders env1 bs  in
                      (match uu____8423 with
                       | (bs1,envbody,g,uu____8455) ->
                           let uu____8456 =
                             FStar_TypeChecker_Env.clear_expected_typ envbody
                              in
                           (match uu____8456 with
                            | (envbody1,uu____8484) ->
                                ((FStar_Pervasives_Native.Some t2), bs1, [],
                                  FStar_Pervasives_Native.None, envbody1,
                                  body1, g)))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____8495;
                         FStar_Syntax_Syntax.pos = uu____8496;
                         FStar_Syntax_Syntax.vars = uu____8497;_},uu____8498)
                      ->
                      let uu____8535 =
                        match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8542 -> failwith "Impossible"  in
                      let uu____8551 = tc_binders env1 bs  in
                      (match uu____8551 with
                       | (bs1,envbody,g,uu____8583) ->
                           let uu____8584 =
                             FStar_TypeChecker_Env.clear_expected_typ envbody
                              in
                           (match uu____8584 with
                            | (envbody1,uu____8612) ->
                                ((FStar_Pervasives_Native.Some t2), bs1, [],
                                  FStar_Pervasives_Native.None, envbody1,
                                  body1, g)))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____8624) ->
                      let uu____8629 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____8629 with
                       | (uu____8670,bs1,bs',copt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____8713 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____8713 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____8829 c_expected2 body3
                               =
                               match uu____8829 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____8949 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env3, bs2, guard, uu____8949, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____8980 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____8980
                                           in
                                        let uu____8981 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env3, bs2, guard, uu____8981, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____9006 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____9006
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
                                               let uu____9058 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____9058 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____9081 =
                                                      check_binders env3
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____9081 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____9131 =
                                                           let uu____9162 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard'
                                                              in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____9162,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____9131
                                                           c_expected4 body3))
                                           | uu____9179 ->
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
                             let uu____9195 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____9195 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___85_9255 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___85_9255.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___85_9255.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___85_9255.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___85_9255.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___85_9255.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___85_9255.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___85_9255.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___85_9255.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___85_9255.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___85_9255.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___85_9255.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___85_9255.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___85_9255.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___85_9255.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___85_9255.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___85_9255.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___85_9255.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___85_9255.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___85_9255.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___85_9255.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___85_9255.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___85_9255.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___85_9255.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___85_9255.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___85_9255.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___85_9255.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___85_9255.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___85_9255.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___85_9255.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___85_9255.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___85_9255.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___85_9255.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___85_9255.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___85_9255.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___85_9255.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___85_9255.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____9303  ->
                                     fun uu____9304  ->
                                       match (uu____9303, uu____9304) with
                                       | ((env2,letrec_binders),(l,t3,u_names))
                                           ->
                                           let uu____9366 =
                                             let uu____9373 =
                                               let uu____9374 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2
                                                  in
                                               FStar_All.pipe_right
                                                 uu____9374
                                                 FStar_Pervasives_Native.fst
                                                in
                                             tc_term uu____9373 t3  in
                                           (match uu____9366 with
                                            | (t4,uu____9396,uu____9397) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (u_names, t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____9407 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___86_9410 =
                                                             x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___86_9410.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___86_9410.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____9407 ::
                                                        letrec_binders
                                                  | uu____9411 ->
                                                      letrec_binders
                                                   in
                                                (env3, lb))) (envbody1, []))
                              in
                           let uu____9416 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____9416 with
                            | (envbody,bs1,g,c,body2) ->
                                let uu____9470 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____9470 with
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
                  | uu____9516 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____9537 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2  in
                        as_function_typ true uu____9537
                      else
                        (let uu____9539 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____9539 with
                         | (uu____9578,bs1,uu____9580,c_opt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____9600 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____9600 with
          | (env1,topt) ->
              let uu____9619 =
                let uu____9620 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____9620
                then
                  let uu____9621 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____9621
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ()  in
              let uu____9625 = expected_function_typ1 env1 topt body  in
              (match uu____9625 with
               | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                   let uu____9665 =
                     let should_check_expected_effect =
                       let uu____9673 =
                         let uu____9680 =
                           let uu____9681 = FStar_Syntax_Subst.compress body1
                              in
                           uu____9681.FStar_Syntax_Syntax.n  in
                         (c_opt, uu____9680)  in
                       match uu____9673 with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Syntax_Syntax.Tm_ascribed
                          (uu____9686,(FStar_Util.Inr expected_c,uu____9688),uu____9689))
                           -> false
                       | uu____9738 -> true  in
                     let uu____9745 =
                       tc_term
                         (let uu___87_9754 = envbody  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___87_9754.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___87_9754.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___87_9754.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___87_9754.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___87_9754.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___87_9754.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___87_9754.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___87_9754.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___87_9754.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___87_9754.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___87_9754.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___87_9754.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___87_9754.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level = false;
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___87_9754.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq = use_eq;
                            FStar_TypeChecker_Env.is_iface =
                              (uu___87_9754.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___87_9754.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___87_9754.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___87_9754.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.failhard =
                              (uu___87_9754.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___87_9754.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___87_9754.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___87_9754.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___87_9754.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___87_9754.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___87_9754.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___87_9754.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___87_9754.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___87_9754.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___87_9754.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___87_9754.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___87_9754.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___87_9754.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___87_9754.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___87_9754.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___87_9754.FStar_TypeChecker_Env.dep_graph)
                          }) body1
                        in
                     match uu____9745 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body
                            in
                         if should_check_expected_effect
                         then
                           let uu____9771 =
                             let uu____9778 =
                               let uu____9783 =
                                 FStar_Syntax_Syntax.lcomp_comp cbody  in
                               (body2, uu____9783)  in
                             check_expected_effect
                               (let uu___88_9786 = envbody  in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___88_9786.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___88_9786.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___88_9786.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___88_9786.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___88_9786.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___88_9786.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___88_9786.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___88_9786.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___88_9786.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___88_9786.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___88_9786.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___88_9786.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___88_9786.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___88_9786.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___88_9786.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___88_9786.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___88_9786.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___88_9786.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___88_9786.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___88_9786.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___88_9786.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___88_9786.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___88_9786.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___88_9786.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___88_9786.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___88_9786.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___88_9786.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___88_9786.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___88_9786.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___88_9786.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___88_9786.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___88_9786.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___88_9786.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___88_9786.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___88_9786.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___88_9786.FStar_TypeChecker_Env.dep_graph)
                                }) c_opt uu____9778
                              in
                           (match uu____9771 with
                            | (body3,cbody1,guard) ->
                                let uu____9796 =
                                  FStar_TypeChecker_Rel.conj_guard
                                    guard_body1 guard
                                   in
                                (body3, cbody1, uu____9796))
                         else
                           (let uu____9798 =
                              FStar_Syntax_Syntax.lcomp_comp cbody  in
                            (body2, uu____9798, guard_body1))
                      in
                   (match uu____9665 with
                    | (body2,cbody,guard) ->
                        let guard1 =
                          let uu____9809 =
                            env1.FStar_TypeChecker_Env.top_level ||
                              (let uu____9811 =
                                 FStar_TypeChecker_Env.should_verify env1  in
                               Prims.op_Negation uu____9811)
                             in
                          if uu____9809
                          then
                            let uu____9812 =
                              FStar_TypeChecker_Rel.conj_guard g guard  in
                            FStar_TypeChecker_Rel.discharge_guard envbody
                              uu____9812
                          else
                            (let guard1 =
                               let uu____9815 =
                                 FStar_TypeChecker_Rel.conj_guard g guard  in
                               FStar_TypeChecker_Rel.close_guard env1
                                 (FStar_List.append bs1 letrec_binders)
                                 uu____9815
                                in
                             guard1)
                           in
                        let tfun_computed = FStar_Syntax_Util.arrow bs1 cbody
                           in
                        let e =
                          FStar_Syntax_Util.abs bs1 body2
                            (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Util.residual_comp_of_comp
                                  (FStar_Util.dflt cbody c_opt)))
                           in
                        let uu____9824 =
                          match tfun_opt with
                          | FStar_Pervasives_Native.Some t ->
                              let t1 = FStar_Syntax_Subst.compress t  in
                              (match t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_arrow uu____9845 ->
                                   (e, t1, guard1)
                               | uu____9858 ->
                                   let uu____9859 =
                                     FStar_TypeChecker_Util.check_and_ascribe
                                       env1 e tfun_computed t1
                                      in
                                   (match uu____9859 with
                                    | (e1,guard') ->
                                        let uu____9872 =
                                          FStar_TypeChecker_Rel.conj_guard
                                            guard1 guard'
                                           in
                                        (e1, t1, uu____9872)))
                          | FStar_Pervasives_Native.None  ->
                              (e, tfun_computed, guard1)
                           in
                        (match uu____9824 with
                         | (e1,tfun,guard2) ->
                             let c = FStar_Syntax_Syntax.mk_Total tfun  in
                             let uu____9885 =
                               let uu____9890 =
                                 FStar_Syntax_Util.lcomp_of_comp c  in
                               FStar_TypeChecker_Util.strengthen_precondition
                                 FStar_Pervasives_Native.None env1 e1
                                 uu____9890 guard2
                                in
                             (match uu____9885 with | (c1,g1) -> (e1, c1, g1)))))

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
              let uu____9935 =
                let uu____9936 =
                  FStar_TypeChecker_Env.debug env FStar_Options.High  in
                if uu____9936
                then
                  let uu____9937 =
                    FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                     in
                  let uu____9938 = FStar_Syntax_Print.term_to_string thead
                     in
                  FStar_Util.print2 "(%s) Type of head is %s\n" uu____9937
                    uu____9938
                else ()  in
              let monadic_application uu____10002 subst1 arg_comps_rev
                arg_rets_rev guard fvs bs =
                match uu____10002 with
                | (head2,chead1,ghead1,cres) ->
                    let rt =
                      check_no_escape (FStar_Pervasives_Native.Some head2)
                        env fvs cres.FStar_Syntax_Syntax.res_typ
                       in
                    let cres1 =
                      let uu___89_10061 = cres  in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___89_10061.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = rt;
                        FStar_Syntax_Syntax.cflags =
                          (uu___89_10061.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___89_10061.FStar_Syntax_Syntax.comp_thunk)
                      }  in
                    let uu____10062 =
                      match bs with
                      | [] ->
                          let g =
                            FStar_TypeChecker_Rel.conj_guard ghead1 guard  in
                          (cres1, g)
                      | uu____10076 ->
                          let g =
                            let uu____10084 =
                              FStar_TypeChecker_Rel.conj_guard ghead1 guard
                               in
                            FStar_All.pipe_right uu____10084
                              (FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env)
                             in
                          let uu____10085 =
                            let uu____10086 =
                              let uu____10089 =
                                let uu____10090 =
                                  FStar_Syntax_Syntax.lcomp_comp cres1  in
                                FStar_Syntax_Util.arrow bs uu____10090  in
                              FStar_Syntax_Syntax.mk_Total uu____10089  in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____10086
                             in
                          (uu____10085, g)
                       in
                    (match uu____10062 with
                     | (cres2,guard1) ->
                         let uu____10103 =
                           let uu____10104 =
                             FStar_TypeChecker_Env.debug env
                               FStar_Options.Low
                              in
                           if uu____10104
                           then
                             let uu____10105 =
                               FStar_Syntax_Print.lcomp_to_string cres2  in
                             FStar_Util.print1
                               "\t Type of result cres is %s\n" uu____10105
                           else ()  in
                         let cres3 =
                           let head_is_pure_and_some_arg_is_effectful =
                             (FStar_Syntax_Util.is_pure_or_ghost_lcomp chead1)
                               &&
                               (FStar_Util.for_some
                                  (fun uu____10121  ->
                                     match uu____10121 with
                                     | (uu____10130,uu____10131,lc) ->
                                         (let uu____10139 =
                                            FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                              lc
                                             in
                                          Prims.op_Negation uu____10139) ||
                                           (FStar_TypeChecker_Util.should_not_inline_lc
                                              lc)) arg_comps_rev)
                              in
                           let term =
                             FStar_Syntax_Syntax.mk_Tm_app head2
                               (FStar_List.rev arg_rets_rev)
                               FStar_Pervasives_Native.None
                               head2.FStar_Syntax_Syntax.pos
                              in
                           let uu____10149 =
                             (FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2)
                               && head_is_pure_and_some_arg_is_effectful
                              in
                           if uu____10149
                           then
                             let uu____10150 =
                               let uu____10151 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme
                                  in
                               if uu____10151
                               then
                                 let uu____10152 =
                                   FStar_Syntax_Print.term_to_string term  in
                                 FStar_Util.print1
                                   "(a) Monadic app: Return inserted in monadic application: %s\n"
                                   uu____10152
                               else ()  in
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env term cres2
                           else
                             (let uu____10155 =
                                let uu____10156 =
                                  FStar_TypeChecker_Env.debug env
                                    FStar_Options.Extreme
                                   in
                                if uu____10156
                                then
                                  let uu____10157 =
                                    FStar_Syntax_Print.term_to_string term
                                     in
                                  FStar_Util.print1
                                    "(a) Monadic app: No return inserted in monadic application: %s\n"
                                    uu____10157
                                else ()  in
                              cres2)
                            in
                         let comp =
                           FStar_List.fold_left
                             (fun out_c  ->
                                fun uu____10181  ->
                                  match uu____10181 with
                                  | ((e,q),x,c) ->
                                      let uu____10206 =
                                        let uu____10207 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Extreme
                                           in
                                        if uu____10207
                                        then
                                          let uu____10208 =
                                            match x with
                                            | FStar_Pervasives_Native.None 
                                                -> "_"
                                            | FStar_Pervasives_Native.Some x1
                                                ->
                                                FStar_Syntax_Print.bv_to_string
                                                  x1
                                             in
                                          let uu____10210 =
                                            FStar_Syntax_Print.term_to_string
                                              e
                                             in
                                          FStar_Util.print2
                                            "(b) Monadic app: Binding argument %s : %s\n"
                                            uu____10208 uu____10210
                                        else ()  in
                                      let uu____10212 =
                                        FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                          c
                                         in
                                      if uu____10212
                                      then
                                        FStar_TypeChecker_Util.bind
                                          e.FStar_Syntax_Syntax.pos env
                                          (FStar_Pervasives_Native.Some e) c
                                          (x, out_c)
                                      else
                                        FStar_TypeChecker_Util.bind
                                          e.FStar_Syntax_Syntax.pos env
                                          FStar_Pervasives_Native.None c
                                          (x, out_c)) cres3 arg_comps_rev
                            in
                         let comp1 =
                           let uu____10219 =
                             let uu____10220 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____10220
                             then
                               let uu____10221 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               FStar_Util.print1
                                 "(c) Monadic app: Binding head %s "
                                 uu____10221
                             else ()  in
                           let uu____10223 =
                             FStar_Syntax_Util.is_pure_or_ghost_lcomp chead1
                              in
                           if uu____10223
                           then
                             FStar_TypeChecker_Util.bind
                               head2.FStar_Syntax_Syntax.pos env
                               (FStar_Pervasives_Native.Some head2) chead1
                               (FStar_Pervasives_Native.None, comp)
                           else
                             FStar_TypeChecker_Util.bind
                               head2.FStar_Syntax_Syntax.pos env
                               FStar_Pervasives_Native.None chead1
                               (FStar_Pervasives_Native.None, comp)
                            in
                         let comp2 =
                           FStar_TypeChecker_Util.subst_lcomp subst1 comp1
                            in
                         let shortcuts_evaluation_order =
                           let uu____10231 =
                             let uu____10232 =
                               FStar_Syntax_Subst.compress head2  in
                             uu____10232.FStar_Syntax_Syntax.n  in
                           match uu____10231 with
                           | FStar_Syntax_Syntax.Tm_fvar fv ->
                               (FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.op_And)
                                 ||
                                 (FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.op_Or)
                           | uu____10236 -> false  in
                         let app =
                           if shortcuts_evaluation_order
                           then
                             let args1 =
                               FStar_List.fold_left
                                 (fun args1  ->
                                    fun uu____10257  ->
                                      match uu____10257 with
                                      | (arg,uu____10271,uu____10272) -> arg
                                          :: args1) [] arg_comps_rev
                                in
                             let app =
                               FStar_Syntax_Syntax.mk_Tm_app head2 args1
                                 FStar_Pervasives_Native.None r
                                in
                             let app1 =
                               FStar_TypeChecker_Util.maybe_lift env app
                                 cres3.FStar_Syntax_Syntax.eff_name
                                 comp2.FStar_Syntax_Syntax.eff_name
                                 comp2.FStar_Syntax_Syntax.res_typ
                                in
                             FStar_TypeChecker_Util.maybe_monadic env app1
                               comp2.FStar_Syntax_Syntax.eff_name
                               comp2.FStar_Syntax_Syntax.res_typ
                           else
                             (let uu____10282 =
                                let map_fun uu____10345 =
                                  match uu____10345 with
                                  | ((e,q),uu____10380,c) ->
                                      let uu____10390 =
                                        FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                          c
                                         in
                                      if uu____10390
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
                                         let uu____10440 =
                                           let uu____10445 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10445, q)  in
                                         ((FStar_Pervasives_Native.Some
                                             (x,
                                               (c.FStar_Syntax_Syntax.eff_name),
                                               (c.FStar_Syntax_Syntax.res_typ),
                                               e1)), uu____10440))
                                   in
                                let uu____10474 =
                                  let uu____10499 =
                                    let uu____10522 =
                                      let uu____10537 =
                                        let uu____10546 =
                                          FStar_Syntax_Syntax.as_arg head2
                                           in
                                        (uu____10546,
                                          FStar_Pervasives_Native.None,
                                          chead1)
                                         in
                                      uu____10537 :: arg_comps_rev  in
                                    FStar_List.map map_fun uu____10522  in
                                  FStar_All.pipe_left FStar_List.split
                                    uu____10499
                                   in
                                match uu____10474 with
                                | (lifted_args,reverse_args) ->
                                    let uu____10719 =
                                      let uu____10720 =
                                        FStar_List.hd reverse_args  in
                                      FStar_Pervasives_Native.fst uu____10720
                                       in
                                    let uu____10729 =
                                      let uu____10736 =
                                        FStar_List.tl reverse_args  in
                                      FStar_List.rev uu____10736  in
                                    (lifted_args, uu____10719, uu____10729)
                                 in
                              match uu____10282 with
                              | (lifted_args,head3,args1) ->
                                  let app =
                                    FStar_Syntax_Syntax.mk_Tm_app head3 args1
                                      FStar_Pervasives_Native.None r
                                     in
                                  let app1 =
                                    FStar_TypeChecker_Util.maybe_lift env app
                                      cres3.FStar_Syntax_Syntax.eff_name
                                      comp2.FStar_Syntax_Syntax.eff_name
                                      comp2.FStar_Syntax_Syntax.res_typ
                                     in
                                  let app2 =
                                    FStar_TypeChecker_Util.maybe_monadic env
                                      app1 comp2.FStar_Syntax_Syntax.eff_name
                                      comp2.FStar_Syntax_Syntax.res_typ
                                     in
                                  let bind_lifted_args e uu___67_10841 =
                                    match uu___67_10841 with
                                    | FStar_Pervasives_Native.None  -> e
                                    | FStar_Pervasives_Native.Some (x,m,t,e1)
                                        ->
                                        let lb =
                                          FStar_Syntax_Util.mk_letbinding
                                            (FStar_Util.Inl x) [] t m e1 []
                                            e1.FStar_Syntax_Syntax.pos
                                           in
                                        let letbinding =
                                          let uu____10898 =
                                            let uu____10903 =
                                              let uu____10904 =
                                                let uu____10917 =
                                                  let uu____10918 =
                                                    let uu____10919 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x
                                                       in
                                                    [uu____10919]  in
                                                  FStar_Syntax_Subst.close
                                                    uu____10918 e
                                                   in
                                                ((false, [lb]), uu____10917)
                                                 in
                                              FStar_Syntax_Syntax.Tm_let
                                                uu____10904
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____10903
                                             in
                                          uu____10898
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
                                  FStar_List.fold_left bind_lifted_args app2
                                    lifted_args)
                            in
                         let uu____10949 =
                           FStar_TypeChecker_Util.strengthen_precondition
                             FStar_Pervasives_Native.None env app comp2
                             guard1
                            in
                         (match uu____10949 with
                          | (comp3,g) ->
                              let uu____10965 =
                                let uu____10966 =
                                  FStar_TypeChecker_Env.debug env
                                    FStar_Options.Extreme
                                   in
                                if uu____10966
                                then
                                  let uu____10967 =
                                    FStar_Syntax_Print.term_to_string app  in
                                  let uu____10968 =
                                    FStar_Syntax_Print.lcomp_to_string comp3
                                     in
                                  FStar_Util.print2
                                    "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                    uu____10967 uu____10968
                                else ()  in
                              (app, comp3, g)))
                 in
              let rec tc_args head_info uu____11048 bs args1 =
                match uu____11048 with
                | (subst1,outargs,arg_rets,g,fvs) ->
                    (match (bs, args1) with
                     | ((x,FStar_Pervasives_Native.Some
                         (FStar_Syntax_Syntax.Implicit uu____11191))::rest,
                        (uu____11193,FStar_Pervasives_Native.None )::uu____11194)
                         ->
                         let t =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         let t1 =
                           check_no_escape
                             (FStar_Pervasives_Native.Some head1) env fvs t
                            in
                         let uu____11245 =
                           FStar_TypeChecker_Util.new_implicit_var
                             "Instantiating implicit argument in application"
                             head1.FStar_Syntax_Syntax.pos env t1
                            in
                         (match uu____11245 with
                          | (varg,uu____11265,implicits) ->
                              let subst2 = (FStar_Syntax_Syntax.NT (x, varg))
                                :: subst1  in
                              let arg =
                                let uu____11287 =
                                  FStar_Syntax_Syntax.as_implicit true  in
                                (varg, uu____11287)  in
                              let uu____11288 =
                                let uu____11323 =
                                  let uu____11338 =
                                    let uu____11351 =
                                      let uu____11352 =
                                        FStar_Syntax_Syntax.mk_Total t1  in
                                      FStar_All.pipe_right uu____11352
                                        FStar_Syntax_Util.lcomp_of_comp
                                       in
                                    (arg, FStar_Pervasives_Native.None,
                                      uu____11351)
                                     in
                                  uu____11338 :: outargs  in
                                let uu____11371 =
                                  FStar_TypeChecker_Rel.conj_guard implicits
                                    g
                                   in
                                (subst2, uu____11323, (arg :: arg_rets),
                                  uu____11371, fvs)
                                 in
                              tc_args head_info uu____11288 rest args1)
                     | ((x,aqual)::rest,(e,aq)::rest') ->
                         let uu____11458 =
                           match (aqual, aq) with
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit
                              uu____11463),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11464)) ->
                               ()
                           | (FStar_Pervasives_Native.None
                              ,FStar_Pervasives_Native.None ) -> ()
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Equality
                              ),FStar_Pervasives_Native.None ) -> ()
                           | uu____11477 ->
                               let uu____11486 =
                                 let uu____11491 =
                                   let uu____11492 =
                                     FStar_Syntax_Print.aqual_to_string aqual
                                      in
                                   let uu____11493 =
                                     FStar_Syntax_Print.aqual_to_string aq
                                      in
                                   let uu____11494 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____11495 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   FStar_Util.format4
                                     "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                     uu____11492 uu____11493 uu____11494
                                     uu____11495
                                    in
                                 (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                   uu____11491)
                                  in
                               FStar_Errors.raise_error uu____11486
                                 e.FStar_Syntax_Syntax.pos
                            in
                         let targ =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         let x1 =
                           let uu___90_11498 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___90_11498.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___90_11498.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = targ
                           }  in
                         let uu____11499 =
                           let uu____11500 =
                             FStar_TypeChecker_Env.debug env
                               FStar_Options.Extreme
                              in
                           if uu____11500
                           then
                             let uu____11501 =
                               FStar_Syntax_Print.term_to_string targ  in
                             FStar_Util.print1
                               "\tType of arg (after subst) = %s\n"
                               uu____11501
                           else ()  in
                         let targ1 =
                           check_no_escape
                             (FStar_Pervasives_Native.Some head1) env fvs
                             targ
                            in
                         let env1 =
                           FStar_TypeChecker_Env.set_expected_typ env targ1
                            in
                         let env2 =
                           let uu___91_11506 = env1  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___91_11506.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___91_11506.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___91_11506.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___91_11506.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___91_11506.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___91_11506.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___91_11506.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___91_11506.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___91_11506.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___91_11506.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___91_11506.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___91_11506.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___91_11506.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___91_11506.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___91_11506.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___91_11506.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___91_11506.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___91_11506.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___91_11506.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___91_11506.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___91_11506.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___91_11506.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___91_11506.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___91_11506.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___91_11506.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___91_11506.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___91_11506.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___91_11506.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___91_11506.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___91_11506.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___91_11506.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___91_11506.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___91_11506.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___91_11506.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___91_11506.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___91_11506.FStar_TypeChecker_Env.dep_graph)
                           }  in
                         let uu____11507 =
                           let uu____11508 =
                             FStar_TypeChecker_Env.debug env2
                               FStar_Options.High
                              in
                           if uu____11508
                           then
                             let uu____11509 =
                               FStar_Syntax_Print.tag_of_term e  in
                             let uu____11510 =
                               FStar_Syntax_Print.term_to_string e  in
                             let uu____11511 =
                               FStar_Syntax_Print.term_to_string targ1  in
                             FStar_Util.print3
                               "Checking arg (%s) %s at type %s\n"
                               uu____11509 uu____11510 uu____11511
                           else ()  in
                         let uu____11513 = tc_term env2 e  in
                         (match uu____11513 with
                          | (e1,c,g_e) ->
                              let g1 = FStar_TypeChecker_Rel.conj_guard g g_e
                                 in
                              let arg = (e1, aq)  in
                              let xterm =
                                let uu____11548 =
                                  let uu____11551 =
                                    let uu____11558 =
                                      FStar_Syntax_Syntax.bv_to_name x1  in
                                    FStar_Syntax_Syntax.as_arg uu____11558
                                     in
                                  FStar_Pervasives_Native.fst uu____11551  in
                                (uu____11548, aq)  in
                              let uu____11565 =
                                (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) ||
                                  (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                     env2 c.FStar_Syntax_Syntax.eff_name)
                                 in
                              if uu____11565
                              then
                                let subst2 =
                                  let uu____11573 = FStar_List.hd bs  in
                                  maybe_extend_subst subst1 uu____11573 e1
                                   in
                                tc_args head_info
                                  (subst2,
                                    ((arg, (FStar_Pervasives_Native.Some x1),
                                       c) :: outargs), (xterm :: arg_rets),
                                    g1, fvs) rest rest'
                              else
                                tc_args head_info
                                  (subst1,
                                    ((arg, (FStar_Pervasives_Native.Some x1),
                                       c) :: outargs), (xterm :: arg_rets),
                                    g1, (x1 :: fvs)) rest rest')
                     | (uu____11699,[]) ->
                         monadic_application head_info subst1 outargs
                           arg_rets g fvs bs
                     | ([],arg::uu____11731) ->
                         let uu____11774 =
                           monadic_application head_info subst1 outargs
                             arg_rets g fvs []
                            in
                         (match uu____11774 with
                          | (head2,chead1,ghead1) ->
                              let rec aux norm1 tres =
                                let tres1 =
                                  let uu____11810 =
                                    FStar_Syntax_Subst.compress tres  in
                                  FStar_All.pipe_right uu____11810
                                    FStar_Syntax_Util.unrefine
                                   in
                                match tres1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_arrow (bs1,cres') ->
                                    let uu____11835 =
                                      FStar_Syntax_Subst.open_comp bs1 cres'
                                       in
                                    (match uu____11835 with
                                     | (bs2,cres'1) ->
                                         let head_info1 =
                                           let uu____11857 =
                                             FStar_Syntax_Util.lcomp_of_comp
                                               cres'1
                                              in
                                           (head2, chead1, ghead1,
                                             uu____11857)
                                            in
                                         let uu____11858 =
                                           let uu____11859 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Low
                                              in
                                           if uu____11859
                                           then
                                             FStar_Errors.log_issue
                                               tres1.FStar_Syntax_Syntax.pos
                                               (FStar_Errors.Warning_RedundantExplicitCurrying,
                                                 "Potentially redundant explicit currying of a function type")
                                           else ()  in
                                         tc_args head_info1
                                           ([], [], [],
                                             FStar_TypeChecker_Rel.trivial_guard,
                                             []) bs2 args1)
                                | uu____11901 when Prims.op_Negation norm1 ->
                                    let rec norm_tres tres2 =
                                      let tres3 =
                                        FStar_TypeChecker_Normalize.unfold_whnf
                                          env tres2
                                         in
                                      let uu____11908 =
                                        let uu____11909 =
                                          FStar_Syntax_Subst.compress tres3
                                           in
                                        uu____11909.FStar_Syntax_Syntax.n  in
                                      match uu____11908 with
                                      | FStar_Syntax_Syntax.Tm_refine
                                          ({
                                             FStar_Syntax_Syntax.ppname =
                                               uu____11912;
                                             FStar_Syntax_Syntax.index =
                                               uu____11913;
                                             FStar_Syntax_Syntax.sort = tres4;_},uu____11915)
                                          -> norm_tres tres4
                                      | uu____11922 -> tres3  in
                                    let uu____11923 = norm_tres tres1  in
                                    aux true uu____11923
                                | uu____11924 ->
                                    let uu____11925 =
                                      let uu____11930 =
                                        let uu____11931 =
                                          FStar_TypeChecker_Normalize.term_to_string
                                            env thead
                                           in
                                        let uu____11932 =
                                          FStar_Util.string_of_int n_args  in
                                        FStar_Util.format2
                                          "Too many arguments to function of type %s; got %s arguments"
                                          uu____11931 uu____11932
                                         in
                                      (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                        uu____11930)
                                       in
                                    let uu____11939 =
                                      FStar_Syntax_Syntax.argpos arg  in
                                    FStar_Errors.raise_error uu____11925
                                      uu____11939
                                 in
                              aux false chead1.FStar_Syntax_Syntax.res_typ))
                 in
              let rec check_function_app tf =
                let uu____11957 =
                  let uu____11958 =
                    FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                  uu____11958.FStar_Syntax_Syntax.n  in
                match uu____11957 with
                | FStar_Syntax_Syntax.Tm_uvar uu____11967 ->
                    let bs =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____12005  ->
                              let uu____12012 =
                                let uu____12013 =
                                  let uu____12014 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_right uu____12014
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_TypeChecker_Util.new_uvar env
                                  uu____12013
                                 in
                              FStar_Syntax_Syntax.null_binder uu____12012))
                       in
                    let cres =
                      let t =
                        let uu____12025 =
                          let uu____12026 = FStar_Syntax_Util.type_u ()  in
                          FStar_All.pipe_right uu____12026
                            FStar_Pervasives_Native.fst
                           in
                        FStar_TypeChecker_Util.new_uvar env uu____12025  in
                      let uu____12035 = FStar_Options.ml_ish ()  in
                      if uu____12035
                      then FStar_Syntax_Util.ml_comp t r
                      else FStar_Syntax_Syntax.mk_Total t  in
                    let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                    let uu____12040 =
                      let uu____12041 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          FStar_Options.Extreme
                         in
                      if uu____12041
                      then
                        let uu____12042 =
                          FStar_Syntax_Print.term_to_string head1  in
                        let uu____12043 =
                          FStar_Syntax_Print.term_to_string tf  in
                        let uu____12044 =
                          FStar_Syntax_Print.term_to_string bs_cres  in
                        FStar_Util.print3
                          "Forcing the type of %s from %s to %s\n"
                          uu____12042 uu____12043 uu____12044
                      else ()  in
                    let uu____12046 =
                      let uu____12047 =
                        FStar_TypeChecker_Rel.teq env tf bs_cres  in
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Rel.force_trivial_guard env)
                        uu____12047
                       in
                    check_function_app bs_cres
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                         uu____12048;
                       FStar_Syntax_Syntax.pos = uu____12049;
                       FStar_Syntax_Syntax.vars = uu____12050;_},uu____12051)
                    ->
                    let bs =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____12109  ->
                              let uu____12116 =
                                let uu____12117 =
                                  let uu____12118 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_right uu____12118
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_TypeChecker_Util.new_uvar env
                                  uu____12117
                                 in
                              FStar_Syntax_Syntax.null_binder uu____12116))
                       in
                    let cres =
                      let t =
                        let uu____12129 =
                          let uu____12130 = FStar_Syntax_Util.type_u ()  in
                          FStar_All.pipe_right uu____12130
                            FStar_Pervasives_Native.fst
                           in
                        FStar_TypeChecker_Util.new_uvar env uu____12129  in
                      let uu____12139 = FStar_Options.ml_ish ()  in
                      if uu____12139
                      then FStar_Syntax_Util.ml_comp t r
                      else FStar_Syntax_Syntax.mk_Total t  in
                    let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                    let uu____12144 =
                      let uu____12145 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          FStar_Options.Extreme
                         in
                      if uu____12145
                      then
                        let uu____12146 =
                          FStar_Syntax_Print.term_to_string head1  in
                        let uu____12147 =
                          FStar_Syntax_Print.term_to_string tf  in
                        let uu____12148 =
                          FStar_Syntax_Print.term_to_string bs_cres  in
                        FStar_Util.print3
                          "Forcing the type of %s from %s to %s\n"
                          uu____12146 uu____12147 uu____12148
                      else ()  in
                    let uu____12150 =
                      let uu____12151 =
                        FStar_TypeChecker_Rel.teq env tf bs_cres  in
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Rel.force_trivial_guard env)
                        uu____12151
                       in
                    check_function_app bs_cres
                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                    let uu____12170 = FStar_Syntax_Subst.open_comp bs c  in
                    (match uu____12170 with
                     | (bs1,c1) ->
                         let head_info =
                           let uu____12192 =
                             FStar_Syntax_Util.lcomp_of_comp c1  in
                           (head1, chead, ghead, uu____12192)  in
                         tc_args head_info
                           ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                             []) bs1 args)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____12234) ->
                    check_function_app bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____12240,uu____12241)
                    -> check_function_app t
                | uu____12282 ->
                    let uu____12283 =
                      FStar_TypeChecker_Err.expected_function_typ env tf  in
                    FStar_Errors.raise_error uu____12283
                      head1.FStar_Syntax_Syntax.pos
                 in
              check_function_app thead

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
                  let uu____12355 =
                    FStar_List.fold_left2
                      (fun uu____12398  ->
                         fun uu____12399  ->
                           fun uu____12400  ->
                             match (uu____12398, uu____12399, uu____12400)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 let uu____12466 =
                                   if aq <> aq'
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ()  in
                                 let uu____12468 =
                                   tc_check_tot_or_gtot_term env e
                                     b.FStar_Syntax_Syntax.sort
                                    in
                                 (match uu____12468 with
                                  | (e1,c1,g) ->
                                      let short =
                                        FStar_TypeChecker_Util.short_circuit
                                          head1 seen
                                         in
                                      let g1 =
                                        let uu____12486 =
                                          FStar_TypeChecker_Rel.guard_of_guard_formula
                                            short
                                           in
                                        FStar_TypeChecker_Rel.imp_guard
                                          uu____12486 g
                                         in
                                      let ghost1 =
                                        ghost ||
                                          ((let uu____12490 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c1
                                               in
                                            Prims.op_Negation uu____12490) &&
                                             (let uu____12492 =
                                                FStar_TypeChecker_Util.is_pure_effect
                                                  env
                                                  c1.FStar_Syntax_Syntax.eff_name
                                                 in
                                              Prims.op_Negation uu____12492))
                                         in
                                      let uu____12493 =
                                        let uu____12502 =
                                          let uu____12511 =
                                            FStar_Syntax_Syntax.as_arg e1  in
                                          [uu____12511]  in
                                        FStar_List.append seen uu____12502
                                         in
                                      let uu____12518 =
                                        FStar_TypeChecker_Rel.conj_guard
                                          guard g1
                                         in
                                      (uu____12493, uu____12518, ghost1)))
                      ([], g_head, false) args bs
                     in
                  (match uu____12355 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____12554 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____12554
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____12556 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____12556 with | (c2,g) -> (e, c2, g)))
              | uu____12574 ->
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
        let uu____12617 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____12617 with
        | (pattern,when_clause,branch_exp) ->
            let uu____12662 = branch1  in
            (match uu____12662 with
             | (cpat,uu____12703,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let tc_annot env1 t =
                     let uu____12775 = FStar_Syntax_Util.type_u ()  in
                     match uu____12775 with
                     | (tu,u) ->
                         let uu____12786 =
                           tc_check_tot_or_gtot_term env1 t tu  in
                         (match uu____12786 with
                          | (t1,uu____12798,g) -> (t1, g))
                      in
                   let uu____12800 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0
                       tc_annot
                      in
                   match uu____12800 with
                   | (pat_bvs1,exp,guard_pat_annots,p) ->
                       let uu____12833 =
                         let uu____12834 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         if uu____12834
                         then
                           let uu____12835 =
                             FStar_Syntax_Print.pat_to_string p0  in
                           let uu____12836 =
                             FStar_Syntax_Print.pat_to_string p  in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____12835 uu____12836
                         else ()  in
                       let pat_env =
                         FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                           env pat_bvs1
                          in
                       let uu____12839 =
                         FStar_TypeChecker_Env.clear_expected_typ pat_env  in
                       (match uu____12839 with
                        | (env1,uu____12861) ->
                            let env11 =
                              let uu___92_12867 = env1  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___92_12867.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___92_12867.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___92_12867.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___92_12867.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___92_12867.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___92_12867.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___92_12867.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___92_12867.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern = true;
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___92_12867.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___92_12867.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___92_12867.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___92_12867.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___92_12867.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___92_12867.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___92_12867.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___92_12867.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___92_12867.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___92_12867.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___92_12867.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___92_12867.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___92_12867.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___92_12867.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___92_12867.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___92_12867.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___92_12867.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___92_12867.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___92_12867.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___92_12867.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___92_12867.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___92_12867.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___92_12867.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___92_12867.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___92_12867.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___92_12867.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___92_12867.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___92_12867.FStar_TypeChecker_Env.dep_graph)
                              }  in
                            let expected_pat_t =
                              FStar_TypeChecker_Rel.unrefine env pat_t  in
                            let uu____12869 =
                              let uu____12870 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.High
                                 in
                              if uu____12870
                              then
                                let uu____12871 =
                                  FStar_Syntax_Print.term_to_string exp  in
                                let uu____12872 =
                                  FStar_Syntax_Print.term_to_string pat_t  in
                                FStar_Util.print2
                                  "Checking pattern expression %s against expected type %s\n"
                                  uu____12871 uu____12872
                              else ()  in
                            let env12 =
                              FStar_TypeChecker_Env.set_expected_typ env11
                                expected_pat_t
                               in
                            let uu____12875 = tc_tot_or_gtot_term env12 exp
                               in
                            (match uu____12875 with
                             | (exp1,lc,g) ->
                                 let g1 =
                                   let uu___93_12900 = g  in
                                   {
                                     FStar_TypeChecker_Env.guard_f =
                                       FStar_TypeChecker_Common.Trivial;
                                     FStar_TypeChecker_Env.deferred =
                                       (uu___93_12900.FStar_TypeChecker_Env.deferred);
                                     FStar_TypeChecker_Env.univ_ineqs =
                                       (uu___93_12900.FStar_TypeChecker_Env.univ_ineqs);
                                     FStar_TypeChecker_Env.implicits =
                                       (uu___93_12900.FStar_TypeChecker_Env.implicits)
                                   }  in
                                 let uu____12901 =
                                   let uu____12902 =
                                     FStar_TypeChecker_Rel.teq_nosmt env12
                                       lc.FStar_Syntax_Syntax.res_typ
                                       expected_pat_t
                                      in
                                   if uu____12902
                                   then
                                     let env13 =
                                       FStar_TypeChecker_Env.set_range env12
                                         exp1.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____12904 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         env13 g1
                                        in
                                     FStar_All.pipe_right uu____12904
                                       FStar_TypeChecker_Rel.resolve_implicits
                                   else
                                     (let uu____12906 =
                                        let uu____12911 =
                                          let uu____12912 =
                                            FStar_Syntax_Print.term_to_string
                                              lc.FStar_Syntax_Syntax.res_typ
                                             in
                                          let uu____12913 =
                                            FStar_Syntax_Print.term_to_string
                                              expected_pat_t
                                             in
                                          FStar_Util.format2
                                            "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                            uu____12912 uu____12913
                                           in
                                        (FStar_Errors.Fatal_MismatchedPatternType,
                                          uu____12911)
                                         in
                                      FStar_Errors.raise_error uu____12906
                                        exp1.FStar_Syntax_Syntax.pos)
                                    in
                                 let norm_exp =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.Beta] env12
                                     exp1
                                    in
                                 let uvs_to_string uvs =
                                   let uu____12932 =
                                     let uu____12935 =
                                       FStar_Util.set_elements uvs  in
                                     FStar_All.pipe_right uu____12935
                                       (FStar_List.map
                                          (fun uu____12961  ->
                                             match uu____12961 with
                                             | (u,uu____12967) ->
                                                 FStar_Syntax_Print.uvar_to_string
                                                   u))
                                      in
                                   FStar_All.pipe_right uu____12932
                                     (FStar_String.concat ", ")
                                    in
                                 let uvs1 = FStar_Syntax_Free.uvars norm_exp
                                    in
                                 let uvs2 =
                                   FStar_Syntax_Free.uvars expected_pat_t  in
                                 let uu____12984 =
                                   let uu____12985 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Free")
                                      in
                                   if uu____12985
                                   then
                                     let uu____12986 =
                                       let uu____12987 =
                                         FStar_Syntax_Print.term_to_string
                                           norm_exp
                                          in
                                       let uu____12988 = uvs_to_string uvs1
                                          in
                                       FStar_Util.print2
                                         ">> free_1(%s) = %s\n" uu____12987
                                         uu____12988
                                        in
                                     let uu____12989 =
                                       FStar_Syntax_Print.term_to_string
                                         expected_pat_t
                                        in
                                     let uu____12990 = uvs_to_string uvs2  in
                                     FStar_Util.print2 ">> free_2(%s) = %s\n"
                                       uu____12989 uu____12990
                                   else ()  in
                                 let uu____12992 =
                                   let uu____12993 =
                                     let uu____12994 =
                                       FStar_Util.set_is_subset_of uvs1 uvs2
                                        in
                                     FStar_All.pipe_left Prims.op_Negation
                                       uu____12994
                                      in
                                   if uu____12993
                                   then
                                     let unresolved =
                                       FStar_Util.set_difference uvs1 uvs2
                                        in
                                     let uu____13010 =
                                       let uu____13015 =
                                         let uu____13016 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env norm_exp
                                            in
                                         let uu____13017 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env expected_pat_t
                                            in
                                         let uu____13018 =
                                           uvs_to_string unresolved  in
                                         FStar_Util.format3
                                           "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                           uu____13016 uu____13017
                                           uu____13018
                                          in
                                       (FStar_Errors.Fatal_UnresolvedPatternVar,
                                         uu____13015)
                                        in
                                     FStar_Errors.raise_error uu____13010
                                       p.FStar_Syntax_Syntax.p
                                   else ()  in
                                 let uu____13020 =
                                   let uu____13021 =
                                     FStar_TypeChecker_Env.debug env
                                       FStar_Options.High
                                      in
                                   if uu____13021
                                   then
                                     let uu____13022 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env exp1
                                        in
                                     FStar_Util.print1
                                       "Done checking pattern expression %s\n"
                                       uu____13022
                                   else ()  in
                                 let p1 =
                                   FStar_TypeChecker_Util.decorate_pattern
                                     env p exp1
                                    in
                                 (p1, pat_bvs1, pat_env, exp1,
                                   guard_pat_annots, norm_exp)))
                    in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____13031 =
                   let uu____13038 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____13038
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____13031 with
                  | (scrutinee_env,uu____13071) ->
                      let uu____13076 = tc_pat true pat_t pattern  in
                      (match uu____13076 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,guard_pat_annots,norm_pat_exp)
                           ->
                           let uu____13126 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____13148 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____13148
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____13162 =
                                      let uu____13169 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____13169 e  in
                                    match uu____13162 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____13126 with
                            | (when_clause1,g_when) ->
                                let uu____13212 = tc_term pat_env branch_exp
                                   in
                                (match uu____13212 with
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
                                           let uu____13254 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_18  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_18) uu____13254
                                        in
                                     let uu____13257 =
                                       let eqs =
                                         let uu____13276 =
                                           let uu____13277 =
                                             FStar_TypeChecker_Env.should_verify
                                               env
                                              in
                                           Prims.op_Negation uu____13277  in
                                         if uu____13276
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp
                                               in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____13284 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____13301 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____13302 ->
                                                FStar_Pervasives_Native.None
                                            | uu____13303 ->
                                                let uu____13304 =
                                                  let uu____13305 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____13305 pat_t
                                                    scrutinee_tm e
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____13304)
                                          in
                                       let uu____13306 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch1
                                          in
                                       match uu____13306 with
                                       | (c1,g_branch2) ->
                                           let uu____13331 =
                                             match (eqs, when_condition) with
                                             | uu____13344 when
                                                 let uu____13353 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation
                                                   uu____13353
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
                                                 let uu____13365 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf
                                                    in
                                                 let uu____13366 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when
                                                    in
                                                 (uu____13365, uu____13366)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g_fw =
                                                   let uu____13375 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w
                                                      in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____13375
                                                    in
                                                 let uu____13376 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw
                                                    in
                                                 let uu____13377 =
                                                   let uu____13378 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f
                                                      in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____13378 g_when
                                                    in
                                                 (uu____13376, uu____13377)
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
                                                 let uu____13386 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w
                                                    in
                                                 (uu____13386, g_when)
                                              in
                                           (match uu____13331 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1
                                                   in
                                                let maybe_return_c_weak
                                                  should_return =
                                                  let c_weak1 =
                                                    let uu____13413 =
                                                      should_return &&
                                                        (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                           c_weak)
                                                       in
                                                    if uu____13413
                                                    then
                                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                        env branch_exp1
                                                        c_weak
                                                    else c_weak  in
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak1
                                                   in
                                                let uu____13415 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak
                                                   in
                                                ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                  (c_weak.FStar_Syntax_Syntax.cflags),
                                                  maybe_return_c_weak,
                                                  uu____13415, g_branch2))
                                        in
                                     (match uu____13257 with
                                      | (effect_label,cflags,maybe_return_c,g_when1,g_branch2)
                                          ->
                                          let branch_guard =
                                            let uu____13462 =
                                              let uu____13463 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____13463
                                               in
                                            if uu____13462
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____13497 =
                                                     let uu____13498 =
                                                       let uu____13499 =
                                                         let uu____13502 =
                                                           let uu____13509 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v
                                                              in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____13509
                                                            in
                                                         FStar_Pervasives_Native.snd
                                                           uu____13502
                                                          in
                                                       FStar_List.length
                                                         uu____13499
                                                        in
                                                     uu____13498 >
                                                       (Prims.parse_int "1")
                                                      in
                                                   if uu____13497
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     let uu____13515 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator
                                                        in
                                                     match uu____13515 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____13536 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         let disc1 =
                                                           let uu____13551 =
                                                             let uu____13554
                                                               =
                                                               let uu____13555
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2
                                                                  in
                                                               [uu____13555]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____13554
                                                              in
                                                           uu____13551
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                            in
                                                         let uu____13558 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool
                                                            in
                                                         [uu____13558]
                                                   else []  in
                                                 let fail1 uu____13564 =
                                                   let uu____13565 =
                                                     let uu____13566 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos
                                                        in
                                                     let uu____13567 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1
                                                        in
                                                     let uu____13568 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1
                                                        in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____13566
                                                       uu____13567
                                                       uu____13568
                                                      in
                                                   failwith uu____13565  in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____13580) ->
                                                       head_constructor t1
                                                   | uu____13585 -> fail1 ()
                                                    in
                                                 let pat_exp2 =
                                                   let uu____13587 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____13587
                                                     FStar_Syntax_Util.unmeta
                                                    in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____13590 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____13607;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____13608;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____13609;_},uu____13610)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____13647 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c1 ->
                                                     let uu____13649 =
                                                       let uu____13650 =
                                                         tc_constant env
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c1
                                                          in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____13650
                                                         scrutinee_tm1
                                                         pat_exp2
                                                        in
                                                     [uu____13649]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____13651 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____13659 =
                                                       let uu____13660 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____13660
                                                        in
                                                     if uu____13659
                                                     then []
                                                     else
                                                       (let uu____13664 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13664)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____13667 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____13669 =
                                                       let uu____13670 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____13670
                                                        in
                                                     if uu____13669
                                                     then []
                                                     else
                                                       (let uu____13674 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13674)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1
                                                        in
                                                     let uu____13700 =
                                                       let uu____13701 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____13701
                                                        in
                                                     if uu____13700
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____13708 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____13740
                                                                     ->
                                                                    match uu____13740
                                                                    with
                                                                    | 
                                                                    (ei,uu____13750)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____13756
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____13756
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____13777
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____13791
                                                                    =
                                                                    let uu____13794
                                                                    =
                                                                    let uu____13795
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____13795
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____13796
                                                                    =
                                                                    let uu____13797
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1
                                                                     in
                                                                    [uu____13797]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____13794
                                                                    uu____13796
                                                                     in
                                                                    uu____13791
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13708
                                                            FStar_List.flatten
                                                           in
                                                        let uu____13806 =
                                                          discriminate
                                                            scrutinee_tm1 f
                                                           in
                                                        FStar_List.append
                                                          uu____13806
                                                          sub_term_guards)
                                                 | uu____13809 -> []  in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____13823 =
                                                   let uu____13824 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____13824
                                                    in
                                                 if uu____13823
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____13827 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____13827
                                                       in
                                                    let uu____13832 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    match uu____13832 with
                                                    | (k,uu____13838) ->
                                                        let uu____13839 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k
                                                           in
                                                        (match uu____13839
                                                         with
                                                         | (t1,uu____13847,uu____13848)
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
                                          let uu____13853 =
                                            let uu____13854 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High
                                               in
                                            if uu____13854
                                            then
                                              let uu____13855 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard
                                                 in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____13855
                                            else ()  in
                                          let uu____13857 =
                                            FStar_Syntax_Subst.close_branch
                                              (pattern1, when_clause1,
                                                branch_exp1)
                                             in
                                          (uu____13857, branch_guard,
                                            effect_label, cflags,
                                            maybe_return_c, guard)))))))

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
          let uu____13888 = check_let_bound_def true env1 lb  in
          (match uu____13888 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____13910 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____13927 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____13927, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____13930 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____13930
                        FStar_TypeChecker_Rel.resolve_implicits
                       in
                    let uu____13931 = ()  in
                    let uu____13932 =
                      let uu____13945 =
                        let uu____13960 =
                          let uu____13969 =
                            let uu____13980 =
                              FStar_Syntax_Syntax.lcomp_comp c1  in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____13980)
                             in
                          [uu____13969]  in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____13960
                         in
                      FStar_List.hd uu____13945  in
                    match uu____13932 with
                    | (uu____14025,univs1,e11,c11,gvs) ->
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
                        let uu____14039 = FStar_Syntax_Util.lcomp_of_comp c11
                           in
                        (g13, e11, univs1, uu____14039))
                  in
               (match uu____13910 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____14050 =
                      let uu____14057 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____14057
                      then
                        let uu____14064 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____14064 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               (let uu____14086 =
                                  let uu____14087 =
                                    FStar_TypeChecker_Env.get_range env1  in
                                  FStar_Errors.log_issue uu____14087
                                    FStar_TypeChecker_Err.top_level_effect
                                   in
                                let uu____14088 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_meta
                                       (e2,
                                         (FStar_Syntax_Syntax.Meta_desugared
                                            FStar_Syntax_Syntax.Masked_effect)))
                                    FStar_Pervasives_Native.None
                                    e2.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14088, c12)))
                      else
                        (let uu____14096 =
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g11
                            in
                         let c =
                           let uu____14098 =
                             FStar_Syntax_Syntax.lcomp_comp c11  in
                           FStar_All.pipe_right uu____14098
                             (FStar_TypeChecker_Normalize.normalize_comp
                                [FStar_TypeChecker_Normalize.Beta;
                                FStar_TypeChecker_Normalize.NoFullNorm;
                                FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]
                                env1)
                            in
                         let e21 =
                           let uu____14102 = FStar_Syntax_Util.is_pure_comp c
                              in
                           if uu____14102
                           then e2
                           else
                             (let uu____14106 =
                                let uu____14107 =
                                  FStar_TypeChecker_Env.get_range env1  in
                                FStar_Errors.log_issue uu____14107
                                  FStar_TypeChecker_Err.top_level_effect
                                 in
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta
                                   (e2,
                                     (FStar_Syntax_Syntax.Meta_desugared
                                        FStar_Syntax_Syntax.Masked_effect)))
                                FStar_Pervasives_Native.None
                                e2.FStar_Syntax_Syntax.pos)
                            in
                         (e21, c))
                       in
                    (match uu____14050 with
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
                         let uu____14128 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos
                            in
                         let uu____14141 =
                           FStar_Syntax_Util.lcomp_of_comp cres  in
                         (uu____14128, uu____14141,
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____14144 -> failwith "Impossible"

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
            let uu___94_14175 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___94_14175.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___94_14175.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___94_14175.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___94_14175.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___94_14175.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___94_14175.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___94_14175.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___94_14175.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___94_14175.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___94_14175.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___94_14175.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___94_14175.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___94_14175.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___94_14175.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___94_14175.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___94_14175.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___94_14175.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___94_14175.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___94_14175.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___94_14175.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___94_14175.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___94_14175.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___94_14175.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___94_14175.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___94_14175.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___94_14175.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___94_14175.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___94_14175.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___94_14175.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___94_14175.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___94_14175.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___94_14175.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___94_14175.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___94_14175.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___94_14175.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___94_14175.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____14176 =
            let uu____14187 =
              let uu____14188 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____14188 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____14187 lb  in
          (match uu____14176 with
           | (e1,uu____14210,c1,g1,annotated) ->
               let uu____14214 =
                 let uu____14215 =
                   (FStar_Util.for_some
                      (FStar_Syntax_Util.is_fvar
                         FStar_Parser_Const.inline_let_attr)
                      lb.FStar_Syntax_Syntax.lbattrs)
                     &&
                     (let uu____14217 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp c1  in
                      Prims.op_Negation uu____14217)
                    in
                 if uu____14215
                 then
                   let uu____14218 =
                     let uu____14223 =
                       let uu____14224 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____14225 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____14224 uu____14225
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____14223)
                      in
                   FStar_Errors.raise_error uu____14218
                     e1.FStar_Syntax_Syntax.pos
                 else ()  in
               let x =
                 let uu___95_14228 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___95_14228.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___95_14228.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 }  in
               let uu____14229 =
                 let uu____14234 =
                   let uu____14235 = FStar_Syntax_Syntax.mk_binder x  in
                   [uu____14235]  in
                 FStar_Syntax_Subst.open_term uu____14234 e2  in
               (match uu____14229 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb  in
                    let x1 = FStar_Pervasives_Native.fst xbinder  in
                    let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                    let uu____14255 = tc_term env_x e21  in
                    (match uu____14255 with
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
                           let uu____14280 =
                             let uu____14285 =
                               let uu____14286 =
                                 let uu____14299 =
                                   FStar_Syntax_Subst.close xb e23  in
                                 ((false, [lb1]), uu____14299)  in
                               FStar_Syntax_Syntax.Tm_let uu____14286  in
                             FStar_Syntax_Syntax.mk uu____14285  in
                           uu____14280 FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos
                            in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ
                            in
                         let x_eq_e1 =
                           let uu____14313 =
                             let uu____14314 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ
                                in
                             let uu____14315 =
                               FStar_Syntax_Syntax.bv_to_name x1  in
                             FStar_Syntax_Util.mk_eq2 uu____14314
                               c1.FStar_Syntax_Syntax.res_typ uu____14315 e11
                              in
                           FStar_All.pipe_left
                             (fun _0_19  ->
                                FStar_TypeChecker_Common.NonTrivial _0_19)
                             uu____14313
                            in
                         let g21 =
                           let uu____14317 =
                             let uu____14318 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1
                                in
                             FStar_TypeChecker_Rel.imp_guard uu____14318 g2
                              in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____14317
                            in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21
                            in
                         let uu____14320 =
                           let uu____14321 =
                             FStar_TypeChecker_Env.expected_typ env2  in
                           FStar_Option.isSome uu____14321  in
                         if uu____14320
                         then
                           let tt =
                             let uu____14331 =
                               FStar_TypeChecker_Env.expected_typ env2  in
                             FStar_All.pipe_right uu____14331
                               FStar_Option.get
                              in
                           let uu____14336 =
                             let uu____14337 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports")
                                in
                             if uu____14337
                             then
                               let uu____14338 =
                                 FStar_Syntax_Print.term_to_string tt  in
                               let uu____14339 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ
                                  in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____14338 uu____14339
                             else ()  in
                           (e4, cres, guard)
                         else
                           (let t =
                              check_no_escape FStar_Pervasives_Native.None
                                env2 [x1] cres.FStar_Syntax_Syntax.res_typ
                               in
                            let uu____14343 =
                              let uu____14344 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____14344
                              then
                                let uu____14345 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____14346 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "Checked %s has no escaping types; normalized to %s\n"
                                  uu____14345 uu____14346
                              else ()  in
                            (e4,
                              (let uu___96_14349 = cres  in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___96_14349.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___96_14349.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___96_14349.FStar_Syntax_Syntax.comp_thunk)
                               }), guard)))))
      | uu____14350 -> failwith "Impossible"

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
          let uu____14382 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____14382 with
           | (lbs1,e21) ->
               let uu____14401 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____14401 with
                | (env0,topt) ->
                    let uu____14420 = build_let_rec_env true env0 lbs1  in
                    (match uu____14420 with
                     | (lbs2,rec_env) ->
                         let uu____14439 = check_let_recs rec_env lbs2  in
                         (match uu____14439 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____14459 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs
                                   in
                                FStar_All.pipe_right uu____14459
                                  FStar_TypeChecker_Rel.resolve_implicits
                                 in
                              let all_lb_names =
                                let uu____14465 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____14465
                                  (fun _0_20  ->
                                     FStar_Pervasives_Native.Some _0_20)
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
                                     let uu____14514 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____14554 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____14554)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____14514
                                      in
                                   FStar_List.map2
                                     (fun uu____14588  ->
                                        fun lb  ->
                                          match uu____14588 with
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
                                let uu____14636 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____14636
                                 in
                              let uu____14641 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____14641 with
                               | (lbs5,e22) ->
                                   let uu____14660 =
                                     let uu____14661 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____14661
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1)
                                      in
                                   let uu____14662 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_let
                                          ((true, lbs5), e22))
                                       FStar_Pervasives_Native.None
                                       top.FStar_Syntax_Syntax.pos
                                      in
                                   (uu____14662, cres,
                                     FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____14675 -> failwith "Impossible"

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
          let uu____14707 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____14707 with
           | (lbs1,e21) ->
               let uu____14726 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____14726 with
                | (env0,topt) ->
                    let uu____14745 = build_let_rec_env false env0 lbs1  in
                    (match uu____14745 with
                     | (lbs2,rec_env) ->
                         let uu____14764 = check_let_recs rec_env lbs2  in
                         (match uu____14764 with
                          | (lbs3,g_lbs) ->
                              let uu____14783 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___97_14806 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___97_14806.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___97_14806.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___98_14808 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___98_14808.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___98_14808.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___98_14808.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___98_14808.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___98_14808.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___98_14808.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____14783 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____14835 = tc_term env2 e21  in
                                   (match uu____14835 with
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
                                          let uu____14854 =
                                            let uu____14855 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____14855 g2
                                             in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____14854
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
                                          let uu___99_14859 = cres3  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___99_14859.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___99_14859.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___99_14859.FStar_Syntax_Syntax.comp_thunk)
                                          }  in
                                        let uu____14860 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____14860 with
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
                                                  uu____14896 ->
                                                  (e, cres4, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  let cres5 =
                                                    let uu___100_14901 =
                                                      cres4  in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___100_14901.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___100_14901.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp_thunk
                                                        =
                                                        (uu___100_14901.FStar_Syntax_Syntax.comp_thunk)
                                                    }  in
                                                  (e, cres5, guard)))))))))
      | uu____14904 -> failwith "Impossible"

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
          let uu____14936 = FStar_Options.ml_ish ()  in
          if uu____14936
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____14939 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____14939 with
             | (formals,c) ->
                 let uu____14964 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____14964 with
                  | (actuals,uu____14974,uu____14975) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____14988 =
                          let uu____14993 =
                            let uu____14994 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____14995 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____14994 uu____14995
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____14993)
                           in
                        FStar_Errors.raise_error uu____14988
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____14998 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____14998 actuals
                            in
                         let uu____14999 =
                           if
                             (FStar_List.length formals) <>
                               (FStar_List.length actuals1)
                           then
                             let actuals_msg =
                               let n1 = FStar_List.length actuals1  in
                               if n1 = (Prims.parse_int "1")
                               then "1 argument was found"
                               else
                                 (let uu____15019 =
                                    FStar_Util.string_of_int n1  in
                                  FStar_Util.format1
                                    "%s arguments were found" uu____15019)
                                in
                             let formals_msg =
                               let n1 = FStar_List.length formals  in
                               if n1 = (Prims.parse_int "1")
                               then "1 argument"
                               else
                                 (let uu____15037 =
                                    FStar_Util.string_of_int n1  in
                                  FStar_Util.format1 "%s arguments"
                                    uu____15037)
                                in
                             let msg =
                               let uu____15045 =
                                 FStar_Syntax_Print.term_to_string lbtyp  in
                               let uu____15046 =
                                 FStar_Syntax_Print.lbname_to_string lbname
                                  in
                               FStar_Util.format4
                                 "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                 uu____15045 uu____15046 formals_msg
                                 actuals_msg
                                in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_LetRecArgumentMismatch,
                                 msg) lbdef.FStar_Syntax_Syntax.pos
                           else ()  in
                         let quals =
                           FStar_TypeChecker_Env.lookup_effect_quals env
                             (FStar_Syntax_Util.comp_effect_name c)
                            in
                         FStar_All.pipe_right quals
                           (FStar_List.contains
                              FStar_Syntax_Syntax.TotalEffect))))
           in
        let uu____15053 =
          FStar_List.fold_left
            (fun uu____15079  ->
               fun lb  ->
                 match uu____15079 with
                 | (lbs1,env1) ->
                     let uu____15099 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____15099 with
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
                               let uu____15120 =
                                 let uu____15127 =
                                   let uu____15128 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____15128
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___101_15139 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___101_15139.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___101_15139.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___101_15139.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___101_15139.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___101_15139.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___101_15139.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___101_15139.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___101_15139.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___101_15139.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___101_15139.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___101_15139.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___101_15139.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___101_15139.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___101_15139.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___101_15139.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___101_15139.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___101_15139.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___101_15139.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___101_15139.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___101_15139.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___101_15139.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___101_15139.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___101_15139.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___101_15139.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___101_15139.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___101_15139.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___101_15139.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___101_15139.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___101_15139.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___101_15139.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___101_15139.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___101_15139.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___101_15139.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___101_15139.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___101_15139.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___101_15139.FStar_TypeChecker_Env.dep_graph)
                                    }) t uu____15127
                                  in
                               match uu____15120 with
                               | (t1,uu____15141,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g
                                      in
                                   let uu____15144 =
                                     let uu____15145 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1
                                        in
                                     FStar_All.pipe_left
                                       (fun a246  -> (Obj.magic ()) a246)
                                       uu____15145
                                      in
                                   norm env01 t1)
                             in
                          let env3 =
                            let uu____15147 =
                              termination_check_enabled
                                lb.FStar_Syntax_Syntax.lbname e t1
                               in
                            if uu____15147
                            then
                              let uu___102_15148 = env2  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___102_15148.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___102_15148.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___102_15148.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___102_15148.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___102_15148.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___102_15148.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___102_15148.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___102_15148.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___102_15148.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___102_15148.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___102_15148.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___102_15148.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1,
                                     univ_vars1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___102_15148.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___102_15148.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___102_15148.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___102_15148.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___102_15148.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___102_15148.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___102_15148.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___102_15148.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___102_15148.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___102_15148.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___102_15148.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___102_15148.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___102_15148.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___102_15148.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___102_15148.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___102_15148.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___102_15148.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___102_15148.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___102_15148.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___102_15148.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___102_15148.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___102_15148.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___102_15148.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___102_15148.FStar_TypeChecker_Env.dep_graph)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname
                                (univ_vars1, t1)
                             in
                          let lb1 =
                            let uu___103_15165 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___103_15165.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___103_15165.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___103_15165.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___103_15165.FStar_Syntax_Syntax.lbpos)
                            }  in
                          ((lb1 :: lbs1), env3))) ([], env) lbs
           in
        match uu____15053 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lbs  ->
      let uu____15188 =
        let uu____15197 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____15223 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____15223 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____15251 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____15251
                       | uu____15256 ->
                           let uu____15257 = ()  in
                           let lb1 =
                             let uu___104_15259 = lb  in
                             let uu____15260 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___104_15259.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___104_15259.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___104_15259.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___104_15259.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____15260;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___104_15259.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___104_15259.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____15263 =
                             let uu____15270 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____15270
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____15263 with
                            | (e,c,g) ->
                                let uu____15278 =
                                  let uu____15279 =
                                    let uu____15280 =
                                      FStar_Syntax_Util.is_total_lcomp c  in
                                    Prims.op_Negation uu____15280  in
                                  if uu____15279
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_UnexpectedGTotForLetRec,
                                        "Expected let rec to be a Tot term; got effect GTot")
                                      e.FStar_Syntax_Syntax.pos
                                  else ()  in
                                let lb2 =
                                  FStar_Syntax_Util.mk_letbinding
                                    lb1.FStar_Syntax_Syntax.lbname
                                    lb1.FStar_Syntax_Syntax.lbunivs
                                    lb1.FStar_Syntax_Syntax.lbtyp
                                    FStar_Parser_Const.effect_Tot_lid e
                                    lb1.FStar_Syntax_Syntax.lbattrs
                                    lb1.FStar_Syntax_Syntax.lbpos
                                   in
                                (lb2, g)))))
           in
        FStar_All.pipe_right uu____15197 FStar_List.unzip  in
      match uu____15188 with
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
        let uu____15329 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____15329 with
        | (env1,uu____15347) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____15355 = check_lbtyp top_level env lb  in
            (match uu____15355 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 let uu____15393 =
                   if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                         "Inner let-bound definitions cannot be universe polymorphic")
                       e1.FStar_Syntax_Syntax.pos
                   else ()  in
                 let uu____15395 = ()  in
                 let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                 let uu____15397 =
                   tc_maybe_toplevel_term
                     (let uu___105_15406 = env11  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___105_15406.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___105_15406.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___105_15406.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___105_15406.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___105_15406.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___105_15406.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___105_15406.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___105_15406.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___105_15406.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___105_15406.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___105_15406.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___105_15406.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___105_15406.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level = top_level;
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___105_15406.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___105_15406.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___105_15406.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___105_15406.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___105_15406.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___105_15406.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___105_15406.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___105_15406.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___105_15406.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___105_15406.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___105_15406.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___105_15406.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___105_15406.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___105_15406.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___105_15406.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___105_15406.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___105_15406.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___105_15406.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___105_15406.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___105_15406.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___105_15406.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___105_15406.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.dep_graph =
                          (uu___105_15406.FStar_TypeChecker_Env.dep_graph)
                      }) e11
                    in
                 (match uu____15397 with
                  | (e12,c1,g1) ->
                      let uu____15420 =
                        let uu____15425 =
                          FStar_TypeChecker_Env.set_range env11
                            e12.FStar_Syntax_Syntax.pos
                           in
                        FStar_TypeChecker_Util.strengthen_precondition
                          (FStar_Pervasives_Native.Some
                             (fun uu____15430  ->
                                FStar_Util.return_all
                                  FStar_TypeChecker_Err.ill_kinded_type))
                          uu____15425 e12 c1 wf_annot
                         in
                      (match uu____15420 with
                       | (c11,guard_f) ->
                           let g11 =
                             FStar_TypeChecker_Rel.conj_guard g1 guard_f  in
                           let uu____15444 =
                             let uu____15445 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____15445
                             then
                               let uu____15446 =
                                 FStar_Syntax_Print.lbname_to_string
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu____15447 =
                                 FStar_Syntax_Print.lcomp_to_string c11  in
                               let uu____15448 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   g11
                                  in
                               FStar_Util.print3
                                 "checked let-bound def %s : %s guard is %s\n"
                                 uu____15446 uu____15447 uu____15448
                             else ()  in
                           (e12, univ_vars1, c11, g11,
                             (FStar_Option.isSome topt)))))

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
            let uu____15482 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____15482 with
             | (univ_opening,univ_vars1) ->
                 let uu____15515 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                   univ_opening, uu____15515))
        | uu____15522 ->
            let uu____15523 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____15523 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____15572 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____15572)
                 else
                   (let uu____15580 = FStar_Syntax_Util.type_u ()  in
                    match uu____15580 with
                    | (k,uu____15600) ->
                        let uu____15601 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____15601 with
                         | (t2,uu____15623,g) ->
                             let uu____15625 =
                               let uu____15626 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____15626
                               then
                                 let uu____15627 =
                                   let uu____15628 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____15628
                                    in
                                 let uu____15629 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____15627 uu____15629
                               else ()  in
                             let t3 = norm env1 t2  in
                             let uu____15632 =
                               FStar_TypeChecker_Env.set_expected_typ env1 t3
                                in
                             ((FStar_Pervasives_Native.Some t3), g,
                               univ_vars1, univ_opening, uu____15632))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun uu____15640  ->
      match uu____15640 with
      | (x,imp) ->
          let uu____15659 = FStar_Syntax_Util.type_u ()  in
          (match uu____15659 with
           | (tu,u) ->
               let uu____15678 =
                 let uu____15679 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____15679
                 then
                   let uu____15680 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____15681 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____15682 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____15680 uu____15681 uu____15682
                 else ()  in
               let uu____15684 =
                 tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu
                  in
               (match uu____15684 with
                | (t,uu____15704,g) ->
                    let x1 =
                      ((let uu___106_15712 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___106_15712.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___106_15712.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t
                        }), imp)
                       in
                    let uu____15713 =
                      let uu____15714 =
                        FStar_TypeChecker_Env.debug env FStar_Options.High
                         in
                      if uu____15714
                      then
                        let uu____15715 =
                          FStar_Syntax_Print.bv_to_string
                            (FStar_Pervasives_Native.fst x1)
                           in
                        let uu____15716 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 "Pushing binder %s at type %s\n"
                          uu____15715 uu____15716
                      else ()  in
                    let uu____15718 = push_binding env x1  in
                    (x1, uu____15718, g, u)))

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
            let uu____15810 = tc_binder env1 b  in
            (match uu____15810 with
             | (b1,env',g,u) ->
                 let uu____15851 = aux env' bs2  in
                 (match uu____15851 with
                  | (bs3,env'1,g',us) ->
                      let uu____15904 =
                        let uu____15905 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g'
                           in
                        FStar_TypeChecker_Rel.conj_guard g uu____15905  in
                      ((b1 :: bs3), env'1, uu____15904, (u :: us))))
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
          (fun uu____15992  ->
             fun uu____15993  ->
               match (uu____15992, uu____15993) with
               | ((t,imp),(args1,g)) ->
                   let uu____16062 = tc_term env1 t  in
                   (match uu____16062 with
                    | (t1,uu____16080,g') ->
                        let uu____16082 =
                          FStar_TypeChecker_Rel.conj_guard g g'  in
                        (((t1, imp) :: args1), uu____16082))) args
          ([], FStar_TypeChecker_Rel.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____16124  ->
             match uu____16124 with
             | (pats1,g) ->
                 let uu____16149 = tc_args env p  in
                 (match uu____16149 with
                  | (args,g') ->
                      let uu____16162 = FStar_TypeChecker_Rel.conj_guard g g'
                         in
                      ((args :: pats1), uu____16162))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let uu____16175 = tc_maybe_toplevel_term env e  in
      match uu____16175 with
      | (e1,c,g) ->
          let uu____16191 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____16191
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c  in
             let c2 = norm_c env c1  in
             let uu____16202 =
               let uu____16207 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____16207
               then
                 let uu____16212 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____16212, false)
               else
                 (let uu____16214 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____16214, true))
                in
             match uu____16202 with
             | (target_comp,allow_ghost) ->
                 let uu____16223 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____16223 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____16233 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp  in
                      let uu____16234 =
                        FStar_TypeChecker_Rel.conj_guard g1 g'  in
                      (e1, uu____16233, uu____16234)
                  | uu____16235 ->
                      if allow_ghost
                      then
                        let uu____16244 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2
                           in
                        FStar_Errors.raise_error uu____16244
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____16256 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2
                            in
                         FStar_Errors.raise_error uu____16256
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
      let uu____16279 = tc_tot_or_gtot_term env t  in
      match uu____16279 with
      | (t1,c,g) ->
          let uu____16293 = FStar_TypeChecker_Rel.force_trivial_guard env g
             in
          (t1, c)

let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let uu____16310 =
        let uu____16311 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "RelCheck")
           in
        if uu____16311
        then
          let uu____16312 = FStar_Syntax_Print.term_to_string e  in
          FStar_Util.print1 "Checking term %s\n" uu____16312
        else ()  in
      let env1 =
        let uu___107_16315 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___107_16315.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___107_16315.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___107_16315.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___107_16315.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___107_16315.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___107_16315.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___107_16315.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___107_16315.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___107_16315.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___107_16315.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___107_16315.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___107_16315.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs = [];
          FStar_TypeChecker_Env.top_level = false;
          FStar_TypeChecker_Env.check_uvars =
            (uu___107_16315.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___107_16315.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___107_16315.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___107_16315.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___107_16315.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___107_16315.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard =
            (uu___107_16315.FStar_TypeChecker_Env.failhard);
          FStar_TypeChecker_Env.nosynth =
            (uu___107_16315.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___107_16315.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___107_16315.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___107_16315.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___107_16315.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___107_16315.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___107_16315.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___107_16315.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___107_16315.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___107_16315.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___107_16315.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___107_16315.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___107_16315.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___107_16315.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___107_16315.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___107_16315.FStar_TypeChecker_Env.dep_graph)
        }  in
      let uu____16322 =
        try tc_tot_or_gtot_term env1 e
        with
        | FStar_Errors.Error (e1,msg,uu____16357) ->
            let uu____16358 = FStar_TypeChecker_Env.get_range env1  in
            FStar_Errors.raise_error (e1, msg) uu____16358
         in
      match uu____16322 with
      | (t,c,g) ->
          let uu____16374 = FStar_Syntax_Util.is_total_lcomp c  in
          if uu____16374
          then (t, (c.FStar_Syntax_Syntax.res_typ), g)
          else
            (let uu____16384 =
               let uu____16389 =
                 let uu____16390 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.format1
                   "Implicit argument: Expected a total term; got a ghost term: %s"
                   uu____16390
                  in
               (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____16389)
                in
             let uu____16391 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error uu____16384 uu____16391)
  
let level_of_type_fail :
  'Auu____16406 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____16406
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____16422 =
          let uu____16427 =
            let uu____16428 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____16428 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____16427)  in
        let uu____16429 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____16422 uu____16429
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____16454 =
            let uu____16455 = FStar_Syntax_Util.unrefine t1  in
            uu____16455.FStar_Syntax_Syntax.n  in
          match uu____16454 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____16459 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____16462 = FStar_Syntax_Util.type_u ()  in
                 match uu____16462 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___110_16470 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___110_16470.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___110_16470.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___110_16470.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___110_16470.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___110_16470.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___110_16470.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___110_16470.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___110_16470.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___110_16470.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___110_16470.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___110_16470.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___110_16470.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___110_16470.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___110_16470.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___110_16470.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___110_16470.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___110_16470.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___110_16470.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___110_16470.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___110_16470.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___110_16470.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___110_16470.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___110_16470.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___110_16470.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___110_16470.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___110_16470.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___110_16470.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___110_16470.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___110_16470.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___110_16470.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___110_16470.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___110_16470.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___110_16470.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___110_16470.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___110_16470.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___110_16470.FStar_TypeChecker_Env.dep_graph)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     let uu____16472 =
                       match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____16474 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____16474
                       | uu____16475 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g
                        in
                     u)
           in
        aux true t
  
let rec (universe_of_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun e  ->
      let uu____16488 =
        let uu____16489 = FStar_Syntax_Subst.compress e  in
        uu____16489.FStar_Syntax_Syntax.n  in
      match uu____16488 with
      | FStar_Syntax_Syntax.Tm_bvar uu____16494 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____16499 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____16526 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____16542) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____16565,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____16592) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____16599 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____16599 with | ((uu____16610,t),uu____16612) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____16618 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____16618
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16619,(FStar_Util.Inl t,uu____16621),uu____16622) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16669,(FStar_Util.Inr c,uu____16671),uu____16672) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____16720 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____16729;
             FStar_Syntax_Syntax.vars = uu____16730;_},us)
          ->
          let uu____16736 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____16736 with
           | ((us',t),uu____16749) ->
               let uu____16754 =
                 if (FStar_List.length us) <> (FStar_List.length us')
                 then
                   let uu____16755 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____16755
                 else
                   FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____16771 -> failwith "Impossible") us' us
                  in
               t)
      | FStar_Syntax_Syntax.Tm_uinst uu____16772 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____16782) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____16805 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____16805 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____16825  ->
                      match uu____16825 with
                      | (b,uu____16831) ->
                          let uu____16832 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____16832) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____16837 = universe_of_aux env res  in
                 level_of_type env res uu____16837  in
               let u_c =
                 let uu____16839 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res  in
                 match uu____16839 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____16843 = universe_of_aux env trepr  in
                     level_of_type env trepr uu____16843
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
            | FStar_Syntax_Syntax.Tm_bvar uu____16939 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____16954 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____16993 ->
                let uu____16994 = universe_of_aux env hd3  in
                (uu____16994, args1)
            | FStar_Syntax_Syntax.Tm_name uu____17007 ->
                let uu____17008 = universe_of_aux env hd3  in
                (uu____17008, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____17021 ->
                let uu____17038 = universe_of_aux env hd3  in
                (uu____17038, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____17051 ->
                let uu____17058 = universe_of_aux env hd3  in
                (uu____17058, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____17071 ->
                let uu____17098 = universe_of_aux env hd3  in
                (uu____17098, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____17111 ->
                let uu____17118 = universe_of_aux env hd3  in
                (uu____17118, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____17131 ->
                let uu____17132 = universe_of_aux env hd3  in
                (uu____17132, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____17145 ->
                let uu____17158 = universe_of_aux env hd3  in
                (uu____17158, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____17171 ->
                let uu____17178 = universe_of_aux env hd3  in
                (uu____17178, args1)
            | FStar_Syntax_Syntax.Tm_type uu____17191 ->
                let uu____17192 = universe_of_aux env hd3  in
                (uu____17192, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____17205,hd4::uu____17207) ->
                let uu____17272 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____17272 with
                 | (uu____17287,uu____17288,hd5) ->
                     let uu____17306 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____17306 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____17357 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env e
                   in
                let uu____17359 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____17359 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____17410 ->
                let uu____17411 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____17411 with
                 | (env1,uu____17433) ->
                     let env2 =
                       let uu___111_17439 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___111_17439.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___111_17439.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___111_17439.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___111_17439.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___111_17439.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___111_17439.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___111_17439.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___111_17439.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___111_17439.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___111_17439.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___111_17439.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___111_17439.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___111_17439.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___111_17439.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___111_17439.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___111_17439.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___111_17439.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___111_17439.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___111_17439.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___111_17439.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___111_17439.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___111_17439.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___111_17439.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___111_17439.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___111_17439.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___111_17439.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___111_17439.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___111_17439.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___111_17439.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___111_17439.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___111_17439.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___111_17439.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___111_17439.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___111_17439.FStar_TypeChecker_Env.dep_graph)
                       }  in
                     let uu____17440 =
                       let uu____17441 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____17441
                       then
                         let uu____17442 =
                           let uu____17443 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____17443  in
                         let uu____17444 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____17442 uu____17444
                       else ()  in
                     let uu____17446 = tc_term env2 hd3  in
                     (match uu____17446 with
                      | (uu____17467,{
                                       FStar_Syntax_Syntax.eff_name =
                                         uu____17468;
                                       FStar_Syntax_Syntax.res_typ = t;
                                       FStar_Syntax_Syntax.cflags =
                                         uu____17470;
                                       FStar_Syntax_Syntax.comp_thunk =
                                         uu____17471;_},g)
                          ->
                          let uu____17490 =
                            let uu____17491 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                env2 g
                               in
                            FStar_All.pipe_right uu____17491
                              (fun a247  -> (Obj.magic ()) a247)
                             in
                          (t, args1)))
             in
          let uu____17502 = type_of_head true hd1 args  in
          (match uu____17502 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t
                  in
               let uu____17542 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____17542 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____17586 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____17586)))
      | FStar_Syntax_Syntax.Tm_match (uu____17589,hd1::uu____17591) ->
          let uu____17656 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____17656 with
           | (uu____17659,uu____17660,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____17678,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____17725 = universe_of_aux env e  in
      level_of_type env e uu____17725
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tps  ->
      let uu____17748 = tc_binders env tps  in
      match uu____17748 with
      | (tps1,env1,g,us) ->
          let uu____17767 = FStar_TypeChecker_Rel.force_trivial_guard env1 g
             in
          (tps1, env1, us)
  
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
      let uu____17801 =
        let uu____17802 = FStar_Syntax_Subst.compress t  in
        uu____17802.FStar_Syntax_Syntax.n  in
      match uu____17801 with
      | FStar_Syntax_Syntax.Tm_delayed uu____17807 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____17834 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____17841 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____17841
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____17843 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____17843
            (fun uu____17857  ->
               match uu____17857 with
               | (t1,uu____17865) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____17867;
             FStar_Syntax_Syntax.vars = uu____17868;_},us)
          ->
          let uu____17874 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____17874
            (fun uu____17888  ->
               match uu____17888 with
               | (t1,uu____17896) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____17898 = tc_constant env t.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____17898
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____17900 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____17900
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____17909;_})
          ->
          let mk_comp =
            let uu____17945 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____17945
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____17965 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____17965
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____18012 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____18012
                 (fun u  ->
                    let uu____18020 =
                      let uu____18023 =
                        let uu____18028 =
                          let uu____18029 =
                            let uu____18042 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____18042)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____18029  in
                        FStar_Syntax_Syntax.mk uu____18028  in
                      uu____18023 FStar_Pervasives_Native.None
                        t.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____18020))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____18072 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____18072 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____18122 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____18122
                       (fun uc  ->
                          let uu____18130 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____18130)
                 | (x,imp)::bs3 ->
                     let uu____18148 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____18148
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____18157 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____18175) ->
          let uu____18180 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____18180
            (fun u_x  ->
               let uu____18188 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____18188)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____18225 =
              let uu____18226 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____18226.FStar_Syntax_Syntax.n  in
            match uu____18225 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____18288 = FStar_Util.first_N n_args bs  in
                    match uu____18288 with
                    | (bs1,rest) ->
                        let t1 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____18358 =
                          let uu____18363 = FStar_Syntax_Syntax.mk_Total t1
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____18363  in
                        (match uu____18358 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____18399 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____18399 with
                       | (bs1,c1) ->
                           let uu____18414 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____18414
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____18456  ->
                     match uu____18456 with
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
                         let uu____18502 = FStar_Syntax_Subst.subst subst1 t1
                            in
                         FStar_Pervasives_Native.Some uu____18502)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____18504) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____18510,uu____18511) ->
                aux t1
            | uu____18552 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____18553,(FStar_Util.Inl t1,uu____18555),uu____18556) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____18605,(FStar_Util.Inr c,uu____18607),uu____18608) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (uu____18657,t1) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____18692) ->
          type_of_well_typed_term env t1
      | FStar_Syntax_Syntax.Tm_match uu____18697 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____18720 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____18733 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____18744 = type_of_well_typed_term env t  in
      match uu____18744 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____18750;
            FStar_Syntax_Syntax.vars = uu____18751;_}
          -> FStar_Pervasives_Native.Some u
      | uu____18756 -> FStar_Pervasives_Native.None

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
            let uu___112_18781 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___112_18781.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___112_18781.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___112_18781.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___112_18781.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___112_18781.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___112_18781.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___112_18781.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___112_18781.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___112_18781.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___112_18781.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___112_18781.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___112_18781.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___112_18781.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___112_18781.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___112_18781.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___112_18781.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___112_18781.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___112_18781.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___112_18781.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___112_18781.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___112_18781.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___112_18781.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___112_18781.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___112_18781.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___112_18781.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___112_18781.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___112_18781.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___112_18781.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___112_18781.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___112_18781.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___112_18781.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___112_18781.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___112_18781.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___112_18781.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___112_18781.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___112_18781.FStar_TypeChecker_Env.dep_graph)
            }  in
          let slow_check uu____18786 =
            if must_total
            then
              let uu____18787 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____18787 with | (uu____18794,uu____18795,g) -> g
            else
              (let uu____18798 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____18798 with | (uu____18805,uu____18806,g) -> g)
             in
          let uu____18808 =
            let uu____18809 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____18809  in
          if uu____18808
          then slow_check ()
          else
            (let uu____18811 = type_of_well_typed_term env2 t  in
             match uu____18811 with
             | FStar_Pervasives_Native.None  -> slow_check ()
             | FStar_Pervasives_Native.Some k' ->
                 let uu____18815 =
                   let uu____18816 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                       (FStar_Options.Other "FastImplicits")
                      in
                   if uu____18816
                   then
                     let uu____18817 =
                       FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                        in
                     let uu____18818 = FStar_Syntax_Print.term_to_string t
                        in
                     let uu____18819 = FStar_Syntax_Print.term_to_string k'
                        in
                     let uu____18820 = FStar_Syntax_Print.term_to_string k
                        in
                     FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                       uu____18817 uu____18818 uu____18819 uu____18820
                   else ()  in
                 let b = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                 let uu____18823 =
                   let uu____18824 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                       (FStar_Options.Other "FastImplicits")
                      in
                   if uu____18824
                   then
                     let uu____18825 =
                       FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                        in
                     let uu____18826 = FStar_Syntax_Print.term_to_string t
                        in
                     let uu____18827 = FStar_Syntax_Print.term_to_string k'
                        in
                     let uu____18828 = FStar_Syntax_Print.term_to_string k
                        in
                     FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                       uu____18825 (if b then "succeeded" else "failed")
                       uu____18826 uu____18827 uu____18828
                   else ()  in
                 if b
                 then FStar_TypeChecker_Rel.trivial_guard
                 else slow_check ())
  