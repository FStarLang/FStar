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
             let uu____51 =
               let uu____52 = FStar_Syntax_Syntax.as_arg v1  in
               let uu____53 =
                 let uu____56 = FStar_Syntax_Syntax.as_arg tl1  in [uu____56]
                  in
               uu____52 :: uu____53  in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____51
              in
           uu____46 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
  
let (is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___63_65  ->
    match uu___63_65 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____68 -> false
  
let steps :
  'Auu____75 . 'Auu____75 -> FStar_TypeChecker_Normalize.step Prims.list =
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
            | uu____142 ->
                let t1 = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t1  in
                let uu____150 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____150 with
                 | FStar_Pervasives_Native.None  -> t1
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail1 uu____162 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____164 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____164
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____166 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____167 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____166 uu____167
                             in
                          let uu____168 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____168
                           in
                        let s =
                          let uu____170 =
                            let uu____171 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____171
                             in
                          FStar_TypeChecker_Util.new_uvar env uu____170  in
                        let uu____180 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s  in
                        match uu____180 with
                        | FStar_Pervasives_Native.Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____185 -> fail1 ()))
             in
          aux false kt
  
let push_binding :
  'Auu____194 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____194) FStar_Pervasives_Native.tuple2 ->
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
        let uu____232 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____232
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
        (fun uu____248  ->
           let uu____249 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Util.set_result_typ uu____249 t)
  
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
                let uu____304 = FStar_Syntax_Syntax.mk_Total t  in
                FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____304
            | FStar_Util.Inr lc -> lc  in
          let t = lc.FStar_Syntax_Syntax.res_typ  in
          let uu____313 =
            let uu____320 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____320 with
            | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                let uu____330 =
                  FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                    t'
                   in
                (match uu____330 with
                 | (e1,lc1) ->
                     let t1 = lc1.FStar_Syntax_Syntax.res_typ  in
                     let uu____346 =
                       FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t'
                        in
                     (match uu____346 with
                      | (e2,g) ->
                          ((let uu____360 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____360
                            then
                              let uu____361 =
                                FStar_Syntax_Print.term_to_string t1  in
                              let uu____362 =
                                FStar_Syntax_Print.term_to_string t'  in
                              let uu____363 =
                                FStar_TypeChecker_Rel.guard_to_string env g
                                 in
                              let uu____364 =
                                FStar_TypeChecker_Rel.guard_to_string env
                                  guard
                                 in
                              FStar_Util.print4
                                "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                uu____361 uu____362 uu____363 uu____364
                            else ());
                           (let msg =
                              let uu____372 =
                                FStar_TypeChecker_Rel.is_trivial g  in
                              if uu____372
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
                            let uu____394 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                msg env e2 lc1 g1
                               in
                            match uu____394 with
                            | (lc2,g2) ->
                                let uu____407 = set_lcomp_result lc2 t'  in
                                ((memo_tk e2 t'), uu____407, g2)))))
             in
          match uu____313 with | (e1,lc1,g) -> (e1, lc1, g)
  
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
        let uu____444 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____444 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____454 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____454 with
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
        let uu____506 = ec  in
        match uu____506 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____529 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____529
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____531 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____531
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
            let uu____533 =
              match copt with
              | FStar_Pervasives_Native.Some uu____546 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____549 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____551 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____551))
                     in
                  if uu____549
                  then
                    let uu____558 =
                      let uu____561 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____561  in
                    (uu____558, c)
                  else
                    (let uu____565 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____565
                     then
                       let uu____572 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____572)
                     else
                       (let uu____576 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____576
                        then
                          let uu____583 =
                            let uu____586 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____586  in
                          (uu____583, c)
                        else (FStar_Pervasives_Native.None, c)))
               in
            (match uu____533 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1  in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let c3 =
                        let uu____613 = FStar_Syntax_Util.lcomp_of_comp c2
                           in
                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                          env e uu____613
                         in
                      let c4 = FStar_Syntax_Syntax.lcomp_comp c3  in
                      let uu____615 =
                        FStar_TypeChecker_Util.check_comp env e c4 expected_c
                         in
                      (match uu____615 with
                       | (e1,uu____629,g) ->
                           let g1 =
                             let uu____632 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_TypeChecker_Util.label_guard uu____632
                               "could not prove post-condition" g
                              in
                           ((let uu____634 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low
                                in
                             if uu____634
                             then
                               let uu____635 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               let uu____636 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1
                                  in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____635 uu____636
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c4)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c4)
                                in
                             (e2, expected_c, g1))))))
  
let no_logical_guard :
  'Auu____647 'Auu____648 .
    FStar_TypeChecker_Env.env ->
      ('Auu____647,'Auu____648,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____647,'Auu____648,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____670  ->
      match uu____670 with
      | (te,kt,f) ->
          let uu____680 = FStar_TypeChecker_Rel.guard_form f  in
          (match uu____680 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____688 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____693 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____688 uu____693)
  
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____705 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____705 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____709 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____709
  
let rec (get_pat_vars :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun pats  ->
    fun acc  ->
      let pats1 = FStar_Syntax_Util.unmeta pats  in
      let uu____741 = FStar_Syntax_Util.head_and_args pats1  in
      match uu____741 with
      | (head1,args) ->
          let uu____780 =
            let uu____781 = FStar_Syntax_Util.un_uinst head1  in
            uu____781.FStar_Syntax_Syntax.n  in
          (match uu____780 with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid
               ->
               let uu____788 = FStar_List.tl args  in
               get_pat_vars_args uu____788 acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.smtpatOr_lid
               -> get_pat_vars_args args acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               -> get_pat_vars_args args acc
           | uu____797 ->
               let uu____798 = FStar_Syntax_Free.names pats1  in
               FStar_Util.set_union acc uu____798)

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
  'Auu____833 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,'Auu____833) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____870 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____870
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____871;
                  FStar_Syntax_Syntax.effect_name = uu____872;
                  FStar_Syntax_Syntax.result_typ = uu____873;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____877)::[];
                  FStar_Syntax_Syntax.flags = uu____878;_}
                ->
                let pat_vars =
                  let uu____926 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta] env pats
                     in
                  let uu____927 =
                    FStar_Util.new_set FStar_Syntax_Syntax.order_bv  in
                  get_pat_vars uu____926 uu____927  in
                let uu____930 =
                  FStar_All.pipe_right bs
                    (FStar_Util.find_opt
                       (fun uu____957  ->
                          match uu____957 with
                          | (b,uu____963) ->
                              let uu____964 = FStar_Util.set_mem b pat_vars
                                 in
                              Prims.op_Negation uu____964))
                   in
                (match uu____930 with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some (x,uu____970) ->
                     let uu____975 =
                       let uu____980 =
                         let uu____981 = FStar_Syntax_Print.bv_to_string x
                            in
                         FStar_Util.format1
                           "Pattern misses at least one bound variable: %s"
                           uu____981
                          in
                       (FStar_Errors.Warning_PatternMissingBoundVar,
                         uu____980)
                        in
                     FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       uu____975)
            | uu____982 -> failwith "Impossible"
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
              let uu___70_1038 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___70_1038.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___70_1038.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___70_1038.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___70_1038.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___70_1038.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___70_1038.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___70_1038.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___70_1038.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___70_1038.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___70_1038.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___70_1038.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___70_1038.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___70_1038.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___70_1038.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___70_1038.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___70_1038.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___70_1038.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___70_1038.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___70_1038.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.failhard =
                  (uu___70_1038.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___70_1038.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.tc_term =
                  (uu___70_1038.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___70_1038.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___70_1038.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___70_1038.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___70_1038.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___70_1038.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___70_1038.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___70_1038.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___70_1038.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___70_1038.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___70_1038.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___70_1038.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___70_1038.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___70_1038.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___70_1038.FStar_TypeChecker_Env.dep_graph)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              (let uu____1058 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
               if uu____1058
               then
                 let uu____1059 =
                   FStar_Syntax_Print.binders_to_string ", " bs  in
                 let uu____1060 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____1059 uu____1060
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____1081  ->
                         match uu____1081 with
                         | (b,uu____1089) ->
                             let t =
                               let uu____1091 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort
                                  in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____1091
                                in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____1094 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____1095 -> []
                              | uu____1108 ->
                                  let uu____1109 =
                                    FStar_Syntax_Syntax.bv_to_name b  in
                                  [uu____1109])))
                  in
               let as_lex_list dec =
                 let uu____1116 = FStar_Syntax_Util.head_and_args dec  in
                 match uu____1116 with
                 | (head1,uu____1132) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____1154 -> mk_lex_list [dec])
                  in
               let cflags = FStar_Syntax_Util.comp_flags c  in
               let uu____1158 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___64_1167  ->
                         match uu___64_1167 with
                         | FStar_Syntax_Syntax.DECREASES uu____1168 -> true
                         | uu____1171 -> false))
                  in
               match uu____1158 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____1175 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions  in
                   (match xs with | x::[] -> x | uu____1184 -> mk_lex_list xs))
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____1207 =
              match uu____1207 with
              | (l,t,u_names) ->
                  let uu____1225 =
                    let uu____1226 = FStar_Syntax_Subst.compress t  in
                    uu____1226.FStar_Syntax_Syntax.n  in
                  (match uu____1225 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____1287  ->
                                 match uu____1287 with
                                 | (x,imp) ->
                                     let uu____1298 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____1298
                                     then
                                       let uu____1303 =
                                         let uu____1304 =
                                           let uu____1307 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____1307
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____1304
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____1303, imp)
                                     else (x, imp)))
                          in
                       let uu____1309 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____1309 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____1328 =
                                let uu____1333 =
                                  let uu____1334 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____1335 =
                                    let uu____1338 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____1338]  in
                                  uu____1334 :: uu____1335  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____1333
                                 in
                              uu____1328 FStar_Pervasives_Native.None r  in
                            let uu____1341 = FStar_Util.prefix formals2  in
                            (match uu____1341 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___71_1388 = last1  in
                                   let uu____1389 =
                                     FStar_Syntax_Util.refine last1 precedes1
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___71_1388.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___71_1388.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____1389
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 ((let uu____1415 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low
                                      in
                                   if uu____1415
                                   then
                                     let uu____1416 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____1417 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____1418 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____1416 uu____1417 uu____1418
                                   else ());
                                  (l, t', u_names))))
                   | uu____1422 ->
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
        (let uu___72_2022 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___72_2022.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___72_2022.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___72_2022.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___72_2022.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___72_2022.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___72_2022.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___72_2022.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___72_2022.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___72_2022.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___72_2022.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___72_2022.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___72_2022.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___72_2022.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___72_2022.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___72_2022.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___72_2022.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___72_2022.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___72_2022.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___72_2022.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___72_2022.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___72_2022.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___72_2022.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___72_2022.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___72_2022.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___72_2022.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___72_2022.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___72_2022.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___72_2022.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___72_2022.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___72_2022.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___72_2022.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___72_2022.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___72_2022.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___72_2022.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___72_2022.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___72_2022.FStar_TypeChecker_Env.dep_graph)
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
      (let uu____2034 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____2034
       then
         let uu____2035 =
           let uu____2036 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____2036  in
         let uu____2037 = FStar_Syntax_Print.tag_of_term e  in
         FStar_Util.print2 "%s (%s)\n" uu____2035 uu____2037
       else ());
      (let top = FStar_Syntax_Subst.compress e  in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2046 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____2077 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____2084 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____2101 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____2102 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____2103 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____2104 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____2105 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____2122 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____2135 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____2142 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted
           (uu____2143,{
                         FStar_Syntax_Syntax.qkind =
                           FStar_Syntax_Syntax.Quote_static ;
                         FStar_Syntax_Syntax.antiquotes = aqs;_})
           when
           FStar_List.for_all
             (fun uu____2171  ->
                match uu____2171 with
                | (uu____2180,b,uu____2182) -> Prims.op_Negation b) aqs
           ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl FStar_Syntax_Syntax.t_term)
             FStar_TypeChecker_Rel.trivial_guard
       | FStar_Syntax_Syntax.Tm_quoted uu____2187 ->
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
           let uu____2201 =
             let uu____2208 =
               let uu____2213 = FStar_Syntax_Util.lcomp_of_comp c  in
               FStar_Util.Inr uu____2213  in
             value_check_expected_typ env1 top uu____2208
               FStar_TypeChecker_Rel.trivial_guard
              in
           (match uu____2201 with
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
           let uu____2236 = tc_tot_or_gtot_term env1 e1  in
           (match uu____2236 with
            | (e2,c,g) ->
                let g1 =
                  let uu___73_2253 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___73_2253.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___73_2253.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___73_2253.FStar_TypeChecker_Env.implicits)
                  }  in
                let uu____2254 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____2254, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____2275 = FStar_Syntax_Util.type_u ()  in
           (match uu____2275 with
            | (t,u) ->
                let uu____2288 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____2288 with
                 | (e2,c,g) ->
                     let uu____2304 =
                       let uu____2319 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____2319 with
                       | (env2,uu____2341) -> tc_pats env2 pats  in
                     (match uu____2304 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___74_2375 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___74_2375.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___74_2375.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___74_2375.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____2376 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____2379 =
                            FStar_TypeChecker_Rel.conj_guard g g'1  in
                          (uu____2376, c, uu____2379))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2383) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____2395) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____2414 = tc_term env1 e1  in
           (match uu____2414 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____2438) ->
           let uu____2485 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____2485 with
            | (env0,uu____2499) ->
                let uu____2504 = tc_comp env0 expected_c  in
                (match uu____2504 with
                 | (expected_c1,uu____2518,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1
                        in
                     let uu____2523 =
                       let uu____2530 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res
                          in
                       tc_term uu____2530 e1  in
                     (match uu____2523 with
                      | (e2,c',g') ->
                          let uu____2540 =
                            let uu____2547 =
                              let uu____2552 =
                                FStar_Syntax_Syntax.lcomp_comp c'  in
                              (e2, uu____2552)  in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____2547
                             in
                          (match uu____2540 with
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
                                 let uu____2600 =
                                   FStar_TypeChecker_Rel.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____2600
                                  in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____2612 =
                                            FStar_Syntax_Util.mk_squash
                                              FStar_Syntax_Syntax.U_zero f1
                                             in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____2612)
                                  in
                               let uu____2613 =
                                 comp_check_expected_typ env1 e4 lc  in
                               (match uu____2613 with
                                | (e5,c,f2) ->
                                    let final_guard =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2
                                       in
                                    (e5, c, final_guard))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____2633) ->
           let uu____2680 = FStar_Syntax_Util.type_u ()  in
           (match uu____2680 with
            | (k,u) ->
                let uu____2693 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____2693 with
                 | (t1,uu____2707,f) ->
                     let uu____2709 =
                       let uu____2716 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                       tc_term uu____2716 e1  in
                     (match uu____2709 with
                      | (e2,c,g) ->
                          let uu____2726 =
                            let uu____2731 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____2736  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____2731 e2 c f
                             in
                          (match uu____2726 with
                           | (c1,f1) ->
                               let uu____2745 =
                                 let uu____2752 =
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
                                 comp_check_expected_typ env1 uu____2752 c1
                                  in
                               (match uu____2745 with
                                | (e3,c2,f2) ->
                                    let uu____2792 =
                                      let uu____2793 =
                                        FStar_TypeChecker_Rel.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____2793
                                       in
                                    (e3, c2, uu____2792))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____2794;
              FStar_Syntax_Syntax.vars = uu____2795;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____2858 = FStar_Syntax_Util.head_and_args top  in
           (match uu____2858 with
            | (unary_op,uu____2880) ->
                let head1 =
                  let uu____2904 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2904
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
              FStar_Syntax_Syntax.pos = uu____2942;
              FStar_Syntax_Syntax.vars = uu____2943;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3006 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3006 with
            | (unary_op,uu____3028) ->
                let head1 =
                  let uu____3052 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3052
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
                (FStar_Const.Const_reflect uu____3090);
              FStar_Syntax_Syntax.pos = uu____3091;
              FStar_Syntax_Syntax.vars = uu____3092;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3155 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3155 with
            | (unary_op,uu____3177) ->
                let head1 =
                  let uu____3201 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3201
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
              FStar_Syntax_Syntax.pos = uu____3239;
              FStar_Syntax_Syntax.vars = uu____3240;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3316 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3316 with
            | (unary_op,uu____3338) ->
                let head1 =
                  let uu____3362 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____3362
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
              FStar_Syntax_Syntax.pos = uu____3406;
              FStar_Syntax_Syntax.vars = uu____3407;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____3445 =
             let uu____3452 =
               let uu____3453 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3453  in
             tc_term uu____3452 e1  in
           (match uu____3445 with
            | (e2,c,g) ->
                let uu____3477 = FStar_Syntax_Util.head_and_args top  in
                (match uu____3477 with
                 | (head1,uu____3499) ->
                     let uu____3520 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____3547 =
                       let uu____3548 =
                         let uu____3551 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____3551  in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____3548
                        in
                     (uu____3520, uu____3547, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3556;
              FStar_Syntax_Syntax.vars = uu____3557;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____3610 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3610 with
            | (head1,uu____3632) ->
                let env' =
                  let uu____3654 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____3654  in
                let uu____3655 = tc_term env' r  in
                (match uu____3655 with
                 | (er,uu____3669,gr) ->
                     let uu____3671 = tc_term env1 t  in
                     (match uu____3671 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Rel.conj_guard gr gt1  in
                          let uu____3688 =
                            let uu____3691 =
                              let uu____3696 =
                                let uu____3697 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____3698 =
                                  let uu____3701 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____3701]  in
                                uu____3697 :: uu____3698  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____3696
                               in
                            uu____3691 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____3688, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3706;
              FStar_Syntax_Syntax.vars = uu____3707;_},uu____3708)
           ->
           let uu____3729 =
             let uu____3734 =
               let uu____3735 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____3735  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____3734)  in
           FStar_Errors.raise_error uu____3729 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3742;
              FStar_Syntax_Syntax.vars = uu____3743;_},uu____3744)
           ->
           let uu____3765 =
             let uu____3770 =
               let uu____3771 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____3771  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____3770)  in
           FStar_Errors.raise_error uu____3765 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____3778;
              FStar_Syntax_Syntax.vars = uu____3779;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____3812 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____3812 with
             | (env0,uu____3826) ->
                 let uu____3831 = tc_term env0 e1  in
                 (match uu____3831 with
                  | (e2,c,g) ->
                      let uu____3847 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____3847 with
                       | (reify_op,uu____3869) ->
                           let u_c =
                             let uu____3891 =
                               tc_term env0 c.FStar_Syntax_Syntax.res_typ  in
                             match uu____3891 with
                             | (uu____3898,c',uu____3900) ->
                                 let uu____3901 =
                                   let uu____3902 =
                                     FStar_Syntax_Subst.compress
                                       c'.FStar_Syntax_Syntax.res_typ
                                      in
                                   uu____3902.FStar_Syntax_Syntax.n  in
                                 (match uu____3901 with
                                  | FStar_Syntax_Syntax.Tm_type u -> u
                                  | uu____3906 ->
                                      let uu____3907 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____3907 with
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
                                                 let uu____3919 =
                                                   let uu____3920 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       c'
                                                      in
                                                   let uu____3921 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   let uu____3922 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c'.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   FStar_Util.format3
                                                     "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                     uu____3920 uu____3921
                                                     uu____3922
                                                    in
                                                 failwith uu____3919);
                                            u)))
                              in
                           let repr =
                             let uu____3924 =
                               FStar_Syntax_Syntax.lcomp_comp c  in
                             FStar_TypeChecker_Env.reify_comp env1 uu____3924
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
                             let uu____3945 =
                               FStar_Syntax_Syntax.mk_Total repr  in
                             FStar_All.pipe_right uu____3945
                               FStar_Syntax_Util.lcomp_of_comp
                              in
                           let uu____3946 =
                             comp_check_expected_typ env1 e3 c1  in
                           (match uu____3946 with
                            | (e4,c2,g') ->
                                let uu____3962 =
                                  FStar_TypeChecker_Rel.conj_guard g g'  in
                                (e4, c2, uu____3962))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____3964;
              FStar_Syntax_Syntax.vars = uu____3965;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let no_reflect uu____4009 =
               let uu____4010 =
                 let uu____4015 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____4015)  in
               FStar_Errors.raise_error uu____4010 e1.FStar_Syntax_Syntax.pos
                in
             let uu____4022 = FStar_Syntax_Util.head_and_args top  in
             match uu____4022 with
             | (reflect_op,uu____4044) ->
                 let uu____4065 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____4065 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____4098 =
                        let uu____4099 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable
                           in
                        Prims.op_Negation uu____4099  in
                      if uu____4098
                      then no_reflect ()
                      else
                        (let uu____4109 =
                           FStar_TypeChecker_Env.clear_expected_typ env1  in
                         match uu____4109 with
                         | (env_no_ex,topt) ->
                             let uu____4128 =
                               let u = FStar_TypeChecker_Env.new_u_univ ()
                                  in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr))
                                  in
                               let t =
                                 let uu____4148 =
                                   let uu____4155 =
                                     let uu____4156 =
                                       let uu____4171 =
                                         let uu____4174 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         let uu____4175 =
                                           let uu____4178 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun
                                              in
                                           [uu____4178]  in
                                         uu____4174 :: uu____4175  in
                                       (repr, uu____4171)  in
                                     FStar_Syntax_Syntax.Tm_app uu____4156
                                      in
                                   FStar_Syntax_Syntax.mk uu____4155  in
                                 uu____4148 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let uu____4184 =
                                 let uu____4191 =
                                   let uu____4192 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1
                                      in
                                   FStar_All.pipe_right uu____4192
                                     FStar_Pervasives_Native.fst
                                    in
                                 tc_tot_or_gtot_term uu____4191 t  in
                               match uu____4184 with
                               | (t1,uu____4220,g) ->
                                   let uu____4222 =
                                     let uu____4223 =
                                       FStar_Syntax_Subst.compress t1  in
                                     uu____4223.FStar_Syntax_Syntax.n  in
                                   (match uu____4222 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____4238,(res,uu____4240)::
                                         (wp,uu____4242)::[])
                                        -> (t1, res, wp, g)
                                    | uu____4285 -> failwith "Impossible")
                                in
                             (match uu____4128 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____4316 =
                                    let uu____4321 =
                                      tc_tot_or_gtot_term env_no_ex e1  in
                                    match uu____4321 with
                                    | (e2,c,g) ->
                                        ((let uu____4336 =
                                            let uu____4337 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c
                                               in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____4337
                                             in
                                          if uu____4336
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [(FStar_Errors.Error_UnexpectedGTotComputation,
                                                 "Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____4351 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ
                                             in
                                          match uu____4351 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____4359 =
                                                  let uu____4368 =
                                                    let uu____4375 =
                                                      let uu____4376 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr
                                                         in
                                                      let uu____4377 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____4376 uu____4377
                                                       in
                                                    (FStar_Errors.Error_UnexpectedInstance,
                                                      uu____4375,
                                                      (e2.FStar_Syntax_Syntax.pos))
                                                     in
                                                  [uu____4368]  in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____4359);
                                               (let uu____4390 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                (e2, uu____4390)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____4392 =
                                                let uu____4393 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____4393
                                                 in
                                              (e2, uu____4392)))
                                     in
                                  (match uu____4316 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____4403 =
                                           let uu____4404 =
                                             let uu____4405 =
                                               let uu____4406 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ
                                                  in
                                               [uu____4406]  in
                                             let uu____4407 =
                                               let uu____4416 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp
                                                  in
                                               [uu____4416]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____4405;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____4407;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____4404
                                            in
                                         FStar_All.pipe_right uu____4403
                                           FStar_Syntax_Util.lcomp_of_comp
                                          in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____4436 =
                                         comp_check_expected_typ env1 e3 c
                                          in
                                       (match uu____4436 with
                                        | (e4,c1,g') ->
                                            let uu____4452 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g
                                               in
                                            (e4, c1, uu____4452))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____4499 =
               let uu____4500 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____4500 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____4499 instantiate_both  in
           ((let uu____4516 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____4516
             then
               let uu____4517 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____4518 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____4517
                 uu____4518
             else ());
            (let uu____4520 = tc_term (no_inst env2) head1  in
             match uu____4520 with
             | (head2,chead,g_head) ->
                 let uu____4536 =
                   let uu____4543 =
                     ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                        (let uu____4545 = FStar_Options.lax ()  in
                         Prims.op_Negation uu____4545))
                       && (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____4543
                   then
                     let uu____4552 =
                       let uu____4559 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____4559
                        in
                     match uu____4552 with | (e1,c,g) -> (e1, c, g)
                   else
                     (let uu____4572 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env2 head2 chead g_head args
                        uu____4572)
                    in
                 (match uu____4536 with
                  | (e1,c,g) ->
                      ((let uu____4585 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme
                           in
                        if uu____4585
                        then
                          let uu____4586 =
                            FStar_TypeChecker_Rel.print_pending_implicits g
                             in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____4586
                        else ());
                       (let uu____4588 = comp_check_expected_typ env0 e1 c
                           in
                        match uu____4588 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____4605 =
                                let uu____4606 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____4606.FStar_Syntax_Syntax.n  in
                              match uu____4605 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____4610) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos))
                                     in
                                  let uu___75_4672 =
                                    FStar_TypeChecker_Rel.trivial_guard  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___75_4672.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___75_4672.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___75_4672.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____4721 ->
                                  FStar_TypeChecker_Rel.trivial_guard
                               in
                            let gres =
                              let uu____4723 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp  in
                              FStar_TypeChecker_Rel.conj_guard g uu____4723
                               in
                            ((let uu____4725 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme
                                 in
                              if uu____4725
                              then
                                let uu____4726 =
                                  FStar_Syntax_Print.term_to_string e2  in
                                let uu____4727 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres
                                   in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____4726 uu____4727
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____4767 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____4767 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____4787 = tc_term env12 e1  in
                (match uu____4787 with
                 | (e11,c1,g1) ->
                     let uu____4803 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____4813 = FStar_Syntax_Util.type_u ()  in
                           (match uu____4813 with
                            | (k,uu____4823) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k  in
                                let uu____4825 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t
                                   in
                                (uu____4825, res_t))
                        in
                     (match uu____4803 with
                      | (env_branches,res_t) ->
                          ((let uu____4835 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____4835
                            then
                              let uu____4836 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____4836
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
                            let uu____4949 =
                              let uu____4954 =
                                FStar_List.fold_right
                                  (fun uu____5029  ->
                                     fun uu____5030  ->
                                       match (uu____5029, uu____5030) with
                                       | ((branch1,f,eff_label,cflags,c,g),
                                          (caccum,gaccum)) ->
                                           let uu____5244 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum
                                              in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____5244)) t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard)
                                 in
                              match uu____4954 with
                              | (cases,g) ->
                                  let uu____5342 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____5342, g)
                               in
                            match uu____4949 with
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
                                           (fun uu____5460  ->
                                              match uu____5460 with
                                              | ((pat,wopt,br),uu____5496,eff_label,uu____5498,uu____5499,uu____5500)
                                                  ->
                                                  let uu____5523 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t
                                                     in
                                                  (pat, wopt, uu____5523)))
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
                                  let uu____5578 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____5578
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____5585 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____5585  in
                                     let lb =
                                       let uu____5589 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name
                                          in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_Syntax_Syntax.res_typ
                                         uu____5589 e11 []
                                         e11.FStar_Syntax_Syntax.pos
                                        in
                                     let e2 =
                                       let uu____5595 =
                                         let uu____5602 =
                                           let uu____5603 =
                                             let uu____5616 =
                                               let uu____5617 =
                                                 let uu____5618 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____5618]  in
                                               FStar_Syntax_Subst.close
                                                 uu____5617 e_match
                                                in
                                             ((false, [lb]), uu____5616)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____5603
                                            in
                                         FStar_Syntax_Syntax.mk uu____5602
                                          in
                                       uu____5595
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____5631 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____5631
                                  then
                                    let uu____5632 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____5633 =
                                      FStar_Syntax_Print.lcomp_to_string cres
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____5632 uu____5633
                                  else ());
                                 (let uu____5635 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches
                                     in
                                  (e2, cres, uu____5635))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5638;
                FStar_Syntax_Syntax.lbunivs = uu____5639;
                FStar_Syntax_Syntax.lbtyp = uu____5640;
                FStar_Syntax_Syntax.lbeff = uu____5641;
                FStar_Syntax_Syntax.lbdef = uu____5642;
                FStar_Syntax_Syntax.lbattrs = uu____5643;
                FStar_Syntax_Syntax.lbpos = uu____5644;_}::[]),uu____5645)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____5668),uu____5669) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5684;
                FStar_Syntax_Syntax.lbunivs = uu____5685;
                FStar_Syntax_Syntax.lbtyp = uu____5686;
                FStar_Syntax_Syntax.lbeff = uu____5687;
                FStar_Syntax_Syntax.lbdef = uu____5688;
                FStar_Syntax_Syntax.lbattrs = uu____5689;
                FStar_Syntax_Syntax.lbpos = uu____5690;_}::uu____5691),uu____5692)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____5717),uu____5718) ->
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
        let uu____5744 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5834))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____5893 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_SynthByTacticError,
                  "synth_by_tactic: bad application") rng
           in
        match uu____5744 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____5977 = FStar_TypeChecker_Env.expected_typ env  in
                  (match uu____5977 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____5983 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_SynthByTacticError,
                           "synth_by_tactic: need a type annotation when no expected type is present")
                         uu____5983)
               in
            let uu____5986 = FStar_TypeChecker_Env.clear_expected_typ env  in
            (match uu____5986 with
             | (env',uu____6000) ->
                 let uu____6005 = tc_term env' typ  in
                 (match uu____6005 with
                  | (typ1,uu____6019,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____6022 = tc_tactic env' tau  in
                        match uu____6022 with
                        | (tau1,uu____6036,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let t =
                                if env.FStar_TypeChecker_Env.nosynth
                                then
                                  let uu____6044 =
                                    let uu____6049 =
                                      FStar_TypeChecker_Util.fvar_const env
                                        FStar_Parser_Const.magic_lid
                                       in
                                    let uu____6050 =
                                      let uu____6051 =
                                        FStar_Syntax_Syntax.as_arg
                                          FStar_Syntax_Util.exp_unit
                                         in
                                      [uu____6051]  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6049
                                      uu____6050
                                     in
                                  uu____6044 FStar_Pervasives_Native.None rng
                                else
                                  (let t =
                                     env.FStar_TypeChecker_Env.synth_hook
                                       env' typ1 tau1
                                      in
                                   (let uu____6057 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Tac")
                                       in
                                    if uu____6057
                                    then
                                      let uu____6058 =
                                        FStar_Syntax_Print.term_to_string t
                                         in
                                      FStar_Util.print1 "Got %s\n" uu____6058
                                    else ());
                                   t)
                                 in
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____6061 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng
                                  in
                               tc_term env uu____6061)))))))

and (tc_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___76_6065 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___76_6065.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___76_6065.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___76_6065.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___76_6065.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___76_6065.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___76_6065.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___76_6065.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___76_6065.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___76_6065.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___76_6065.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___76_6065.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___76_6065.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___76_6065.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___76_6065.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___76_6065.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___76_6065.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___76_6065.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___76_6065.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___76_6065.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___76_6065.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___76_6065.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___76_6065.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___76_6065.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___76_6065.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___76_6065.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___76_6065.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___76_6065.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___76_6065.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___76_6065.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___76_6065.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___76_6065.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___76_6065.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___76_6065.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___76_6065.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___76_6065.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___76_6065.FStar_TypeChecker_Env.dep_graph)
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
        let uu___77_6069 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___77_6069.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___77_6069.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___77_6069.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___77_6069.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___77_6069.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___77_6069.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___77_6069.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___77_6069.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___77_6069.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___77_6069.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___77_6069.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___77_6069.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___77_6069.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___77_6069.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___77_6069.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___77_6069.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___77_6069.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___77_6069.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___77_6069.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___77_6069.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___77_6069.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___77_6069.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___77_6069.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___77_6069.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___77_6069.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___77_6069.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___77_6069.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___77_6069.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___77_6069.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___77_6069.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___77_6069.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___77_6069.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___77_6069.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___77_6069.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___77_6069.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___77_6069.FStar_TypeChecker_Env.dep_graph)
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
          let uu____6089 = tc_tactic env tactic  in
          (match uu____6089 with
           | (tactic1,uu____6101,uu____6102) ->
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
        let uu____6151 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____6151 with
        | (e2,t,implicits) ->
            let tc =
              let uu____6172 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____6172
              then FStar_Util.Inl t
              else
                (let uu____6178 =
                   let uu____6179 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____6179
                    in
                 FStar_Util.Inr uu____6178)
               in
            let is_data_ctor uu___65_6191 =
              match uu___65_6191 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____6194) -> true
              | uu____6201 -> false  in
            let uu____6204 =
              (is_data_ctor dc) &&
                (let uu____6206 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____6206)
               in
            if uu____6204
            then
              let uu____6213 =
                let uu____6218 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____6218)  in
              let uu____6219 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____6213 uu____6219
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____6236 =
            let uu____6237 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____6237
             in
          failwith uu____6236
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____6271 =
              let uu____6272 = FStar_Syntax_Subst.compress t1  in
              uu____6272.FStar_Syntax_Syntax.n  in
            match uu____6271 with
            | FStar_Syntax_Syntax.Tm_arrow uu____6275 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____6288 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos))
                   in
                let uu___78_6326 = FStar_TypeChecker_Rel.trivial_guard  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___78_6326.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___78_6326.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___78_6326.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                }
             in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____6378 =
            let uu____6391 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____6391 with
            | FStar_Pervasives_Native.None  ->
                let uu____6406 = FStar_Syntax_Util.type_u ()  in
                (match uu____6406 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard)
             in
          (match uu____6378 with
           | (t,uu____6443,g0) ->
               let uu____6457 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____6457 with
                | (e1,uu____6477,g1) ->
                    let uu____6491 =
                      let uu____6492 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____6492
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____6493 = FStar_TypeChecker_Rel.conj_guard g0 g1
                       in
                    (e1, uu____6491, uu____6493)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____6495 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____6508 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____6508)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____6495 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___79_6527 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___79_6527.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___79_6527.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____6530 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____6530 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____6551 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____6551
                       then FStar_Util.Inl t1
                       else
                         (let uu____6557 =
                            let uu____6558 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____6558
                             in
                          FStar_Util.Inr uu____6557)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6564;
             FStar_Syntax_Syntax.vars = uu____6565;_},uu____6566)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____6571 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____6571
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____6579 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____6579
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6587;
             FStar_Syntax_Syntax.vars = uu____6588;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____6597 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6597 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____6620 =
                     let uu____6625 =
                       let uu____6626 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____6627 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____6628 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____6626 uu____6627 uu____6628
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____6625)
                      in
                   let uu____6629 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____6620 uu____6629)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____6645 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6649 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6649 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6651 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6651 with
           | ((us,t),range) ->
               ((let uu____6674 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____6674
                 then
                   let uu____6675 =
                     let uu____6676 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____6676  in
                   let uu____6677 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____6678 = FStar_Range.string_of_range range  in
                   let uu____6679 = FStar_Range.string_of_use_range range  in
                   let uu____6680 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____6675 uu____6677 uu____6678 uu____6679 uu____6680
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6685 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6685 us  in
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
          let uu____6709 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6709 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____6723 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____6723 with
                | (env2,uu____6737) ->
                    let uu____6742 = tc_binders env2 bs1  in
                    (match uu____6742 with
                     | (bs2,env3,g,us) ->
                         let uu____6761 = tc_comp env3 c1  in
                         (match uu____6761 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___80_6780 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___80_6780.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___80_6780.FStar_Syntax_Syntax.vars)
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
                                  let uu____6789 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____6789
                                   in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g1))))))
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
          let uu____6808 =
            let uu____6813 =
              let uu____6814 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____6814]  in
            FStar_Syntax_Subst.open_term uu____6813 phi  in
          (match uu____6808 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____6824 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____6824 with
                | (env2,uu____6838) ->
                    let uu____6843 =
                      let uu____6856 = FStar_List.hd x1  in
                      tc_binder env2 uu____6856  in
                    (match uu____6843 with
                     | (x2,env3,f1,u) ->
                         ((let uu____6884 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____6884
                           then
                             let uu____6885 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____6886 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____6887 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____6885 uu____6886 uu____6887
                           else ());
                          (let uu____6889 = FStar_Syntax_Util.type_u ()  in
                           match uu____6889 with
                           | (t_phi,uu____6901) ->
                               let uu____6902 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____6902 with
                                | (phi2,uu____6916,f2) ->
                                    let e1 =
                                      let uu___81_6921 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___81_6921.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___81_6921.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____6928 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____6928
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____6941) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____6964 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
            if uu____6964
            then
              let uu____6965 =
                FStar_Syntax_Print.term_to_string
                  (let uu___82_6968 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___82_6968.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___82_6968.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____6965
            else ());
           (let uu____6974 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____6974 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____6987 ->
          let uu____6988 =
            let uu____6989 = FStar_Syntax_Print.term_to_string top  in
            let uu____6990 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____6989
              uu____6990
             in
          failwith uu____6988

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____7000 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____7001,FStar_Pervasives_Native.None ) ->
            FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____7012,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____7028 -> FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_float uu____7033 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____7034 ->
            let uu____7035 =
              let uu____7040 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
                 in
              FStar_All.pipe_right uu____7040 FStar_Util.must  in
            FStar_All.pipe_right uu____7035 FStar_Pervasives_Native.fst
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____7065 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____7066 =
              let uu____7071 =
                let uu____7072 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7072
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7071)  in
            FStar_Errors.raise_error uu____7066 r
        | FStar_Const.Const_set_range_of  ->
            let uu____7073 =
              let uu____7078 =
                let uu____7079 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7079
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7078)  in
            FStar_Errors.raise_error uu____7073 r
        | FStar_Const.Const_reify  ->
            let uu____7080 =
              let uu____7085 =
                let uu____7086 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7086
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7085)  in
            FStar_Errors.raise_error uu____7080 r
        | FStar_Const.Const_reflect uu____7087 ->
            let uu____7088 =
              let uu____7093 =
                let uu____7094 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7094
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7093)  in
            FStar_Errors.raise_error uu____7088 r
        | uu____7095 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____7112) ->
          let uu____7121 = FStar_Syntax_Util.type_u ()  in
          (match uu____7121 with
           | (k,u) ->
               let uu____7134 = tc_check_tot_or_gtot_term env t k  in
               (match uu____7134 with
                | (t1,uu____7148,g) ->
                    let uu____7150 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____7150, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____7152) ->
          let uu____7161 = FStar_Syntax_Util.type_u ()  in
          (match uu____7161 with
           | (k,u) ->
               let uu____7174 = tc_check_tot_or_gtot_term env t k  in
               (match uu____7174 with
                | (t1,uu____7188,g) ->
                    let uu____7190 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____7190, u, g)))
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
            let uu____7198 =
              let uu____7203 =
                let uu____7204 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____7204 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____7203  in
            uu____7198 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____7207 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____7207 with
           | (tc1,uu____7221,f) ->
               let uu____7223 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____7223 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____7267 =
                        let uu____7268 = FStar_Syntax_Subst.compress head3
                           in
                        uu____7268.FStar_Syntax_Syntax.n  in
                      match uu____7267 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____7271,us) -> us
                      | uu____7277 -> []  in
                    let uu____7278 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____7278 with
                     | (uu____7299,args1) ->
                         let uu____7321 =
                           let uu____7340 = FStar_List.hd args1  in
                           let uu____7353 = FStar_List.tl args1  in
                           (uu____7340, uu____7353)  in
                         (match uu____7321 with
                          | (res,args2) ->
                              let uu____7418 =
                                let uu____7427 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___66_7455  ->
                                          match uu___66_7455 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____7463 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____7463 with
                                               | (env1,uu____7475) ->
                                                   let uu____7480 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____7480 with
                                                    | (e1,uu____7492,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____7427
                                  FStar_List.unzip
                                 in
                              (match uu____7418 with
                               | (flags1,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___83_7531 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___83_7531.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___83_7531.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____7535 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u
                                        in
                                     match uu____7535 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let uu____7539 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____7539))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____7549 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____7550 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____7560 = aux u3  in FStar_Syntax_Syntax.U_succ uu____7560
        | FStar_Syntax_Syntax.U_max us ->
            let uu____7564 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____7564
        | FStar_Syntax_Syntax.U_name x ->
            let uu____7568 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____7568
            then u2
            else
              (let uu____7570 =
                 let uu____7571 =
                   let uu____7572 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.strcat uu____7572 " not found"  in
                 Prims.strcat "Universe variable " uu____7571  in
               failwith uu____7570)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____7574 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____7574 FStar_Pervasives_Native.snd
         | uu____7583 -> aux u)

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
            let uu____7612 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____7612 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____7718 bs2 bs_expected1 =
              match uu____7718 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____7886)) ->
                             let uu____7891 =
                               let uu____7896 =
                                 let uu____7897 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____7897
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____7896)
                                in
                             let uu____7898 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____7891 uu____7898
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____7899),FStar_Pervasives_Native.None ) ->
                             let uu____7904 =
                               let uu____7909 =
                                 let uu____7910 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____7910
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____7909)
                                in
                             let uu____7911 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____7904 uu____7911
                         | uu____7912 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____7918 =
                           let uu____7923 =
                             let uu____7924 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____7924.FStar_Syntax_Syntax.n  in
                           match uu____7923 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____7931 ->
                               ((let uu____7933 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____7933
                                 then
                                   let uu____7934 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____7934
                                 else ());
                                (let uu____7936 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____7936 with
                                 | (t,uu____7948,g1) ->
                                     let g2 =
                                       let uu____7951 =
                                         FStar_TypeChecker_Rel.teq_nosmt env2
                                           t expected_t
                                          in
                                       if uu____7951
                                       then
                                         FStar_TypeChecker_Rel.trivial_guard
                                       else
                                         (let uu____7953 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t
                                             in
                                          match uu____7953 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____7956 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t
                                                 in
                                              let uu____7961 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_Errors.raise_error
                                                uu____7956 uu____7961
                                          | FStar_Pervasives_Native.Some g2
                                              ->
                                              let uu____7963 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____7963
                                                "Type annotation on parameter incompatible with the expected type"
                                                g2)
                                        in
                                     let g3 =
                                       let uu____7965 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2
                                          in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____7965
                                        in
                                     (t, g3)))
                            in
                         match uu____7918 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___84_7993 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___84_7993.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___84_7993.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env3 = push_binding env2 b  in
                             let subst2 =
                               let uu____8006 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____8006
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
                  | uu____8160 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____8169 = tc_binders env1 bs  in
                  match uu____8169 with
                  | (bs1,envbody,g,uu____8199) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____8247 =
                    let uu____8248 = FStar_Syntax_Subst.compress t2  in
                    uu____8248.FStar_Syntax_Syntax.n  in
                  match uu____8247 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____8271 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8295 -> failwith "Impossible");
                       (let uu____8304 = tc_binders env1 bs  in
                        match uu____8304 with
                        | (bs1,envbody,g,uu____8336) ->
                            let uu____8337 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____8337 with
                             | (envbody1,uu____8365) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____8376;
                         FStar_Syntax_Syntax.pos = uu____8377;
                         FStar_Syntax_Syntax.vars = uu____8378;_},uu____8379)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8423 -> failwith "Impossible");
                       (let uu____8432 = tc_binders env1 bs  in
                        match uu____8432 with
                        | (bs1,envbody,g,uu____8464) ->
                            let uu____8465 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____8465 with
                             | (envbody1,uu____8493) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____8505) ->
                      let uu____8510 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____8510 with
                       | (uu____8551,bs1,bs',copt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____8594 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____8594 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____8717 c_expected2 body3
                               =
                               match uu____8717 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____8837 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env3, bs2, guard, uu____8837, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____8868 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____8868
                                           in
                                        let uu____8869 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env3, bs2, guard, uu____8869, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____8894 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____8894
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
                                               let uu____8946 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____8946 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____8969 =
                                                      check_binders env3
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____8969 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____9019 =
                                                           let uu____9050 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard'
                                                              in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____9050,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____9019
                                                           c_expected4 body3))
                                           | uu____9067 ->
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
                             let uu____9083 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____9083 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___85_9146 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___85_9146.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___85_9146.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___85_9146.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___85_9146.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___85_9146.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___85_9146.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___85_9146.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___85_9146.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___85_9146.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___85_9146.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___85_9146.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___85_9146.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___85_9146.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___85_9146.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___85_9146.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___85_9146.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___85_9146.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___85_9146.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___85_9146.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___85_9146.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___85_9146.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___85_9146.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___85_9146.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___85_9146.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___85_9146.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___85_9146.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___85_9146.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___85_9146.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___85_9146.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___85_9146.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___85_9146.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___85_9146.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___85_9146.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___85_9146.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___85_9146.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___85_9146.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____9194  ->
                                     fun uu____9195  ->
                                       match (uu____9194, uu____9195) with
                                       | ((env2,letrec_binders),(l,t3,u_names))
                                           ->
                                           let uu____9257 =
                                             let uu____9264 =
                                               let uu____9265 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2
                                                  in
                                               FStar_All.pipe_right
                                                 uu____9265
                                                 FStar_Pervasives_Native.fst
                                                in
                                             tc_term uu____9264 t3  in
                                           (match uu____9257 with
                                            | (t4,uu____9287,uu____9288) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (u_names, t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____9298 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___86_9301 =
                                                             x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___86_9301.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___86_9301.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____9298 ::
                                                        letrec_binders
                                                  | uu____9302 ->
                                                      letrec_binders
                                                   in
                                                (env3, lb))) (envbody1, []))
                              in
                           let uu____9307 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____9307 with
                            | (envbody,bs1,g,c,body2) ->
                                let uu____9361 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____9361 with
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
                  | uu____9407 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____9428 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2  in
                        as_function_typ true uu____9428
                      else
                        (let uu____9430 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____9430 with
                         | (uu____9469,bs1,uu____9471,c_opt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____9491 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____9491 with
          | (env1,topt) ->
              ((let uu____9511 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____9511
                then
                  let uu____9512 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____9512
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____9516 = expected_function_typ1 env1 topt body  in
                match uu____9516 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let uu____9556 =
                      let should_check_expected_effect =
                        let uu____9564 =
                          let uu____9571 =
                            let uu____9572 =
                              FStar_Syntax_Subst.compress body1  in
                            uu____9572.FStar_Syntax_Syntax.n  in
                          (c_opt, uu____9571)  in
                        match uu____9564 with
                        | (FStar_Pervasives_Native.None
                           ,FStar_Syntax_Syntax.Tm_ascribed
                           (uu____9577,(FStar_Util.Inr expected_c,uu____9579),uu____9580))
                            -> false
                        | uu____9629 -> true  in
                      let uu____9636 =
                        tc_term
                          (let uu___87_9645 = envbody  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___87_9645.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___87_9645.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___87_9645.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___87_9645.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___87_9645.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___87_9645.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___87_9645.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___87_9645.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___87_9645.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___87_9645.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___87_9645.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___87_9645.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___87_9645.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = false;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___87_9645.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq = use_eq;
                             FStar_TypeChecker_Env.is_iface =
                               (uu___87_9645.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___87_9645.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___87_9645.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___87_9645.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___87_9645.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___87_9645.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___87_9645.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___87_9645.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___87_9645.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___87_9645.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___87_9645.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___87_9645.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___87_9645.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___87_9645.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___87_9645.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___87_9645.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___87_9645.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___87_9645.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___87_9645.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___87_9645.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___87_9645.FStar_TypeChecker_Env.dep_graph)
                           }) body1
                         in
                      match uu____9636 with
                      | (body2,cbody,guard_body) ->
                          let guard_body1 =
                            FStar_TypeChecker_Rel.solve_deferred_constraints
                              envbody guard_body
                             in
                          if should_check_expected_effect
                          then
                            let uu____9662 =
                              let uu____9669 =
                                let uu____9674 =
                                  FStar_Syntax_Syntax.lcomp_comp cbody  in
                                (body2, uu____9674)  in
                              check_expected_effect
                                (let uu___88_9677 = envbody  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___88_9677.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___88_9677.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___88_9677.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___88_9677.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___88_9677.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___88_9677.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___88_9677.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___88_9677.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___88_9677.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___88_9677.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___88_9677.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___88_9677.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___88_9677.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___88_9677.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___88_9677.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___88_9677.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___88_9677.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___88_9677.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___88_9677.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___88_9677.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___88_9677.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___88_9677.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___88_9677.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___88_9677.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___88_9677.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___88_9677.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___88_9677.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___88_9677.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___88_9677.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___88_9677.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___88_9677.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___88_9677.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___88_9677.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___88_9677.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___88_9677.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___88_9677.FStar_TypeChecker_Env.dep_graph)
                                 }) c_opt uu____9669
                               in
                            (match uu____9662 with
                             | (body3,cbody1,guard) ->
                                 let uu____9687 =
                                   FStar_TypeChecker_Rel.conj_guard
                                     guard_body1 guard
                                    in
                                 (body3, cbody1, uu____9687))
                          else
                            (let uu____9689 =
                               FStar_Syntax_Syntax.lcomp_comp cbody  in
                             (body2, uu____9689, guard_body1))
                       in
                    (match uu____9556 with
                     | (body2,cbody,guard) ->
                         let guard1 =
                           let uu____9700 =
                             env1.FStar_TypeChecker_Env.top_level ||
                               (let uu____9702 =
                                  FStar_TypeChecker_Env.should_verify env1
                                   in
                                Prims.op_Negation uu____9702)
                              in
                           if uu____9700
                           then
                             let uu____9703 =
                               FStar_TypeChecker_Rel.conj_guard g guard  in
                             FStar_TypeChecker_Rel.discharge_guard envbody
                               uu____9703
                           else
                             (let guard1 =
                                let uu____9706 =
                                  FStar_TypeChecker_Rel.conj_guard g guard
                                   in
                                FStar_TypeChecker_Rel.close_guard env1
                                  (FStar_List.append bs1 letrec_binders)
                                  uu____9706
                                 in
                              guard1)
                            in
                         let tfun_computed =
                           FStar_Syntax_Util.arrow bs1 cbody  in
                         let e =
                           FStar_Syntax_Util.abs bs1 body2
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp
                                   (FStar_Util.dflt cbody c_opt)))
                            in
                         let uu____9715 =
                           match tfun_opt with
                           | FStar_Pervasives_Native.Some t ->
                               let t1 = FStar_Syntax_Subst.compress t  in
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_arrow uu____9736 ->
                                    (e, t1, guard1)
                                | uu____9749 ->
                                    let uu____9750 =
                                      FStar_TypeChecker_Util.check_and_ascribe
                                        env1 e tfun_computed t1
                                       in
                                    (match uu____9750 with
                                     | (e1,guard') ->
                                         let uu____9763 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 guard'
                                            in
                                         (e1, t1, uu____9763)))
                           | FStar_Pervasives_Native.None  ->
                               (e, tfun_computed, guard1)
                            in
                         (match uu____9715 with
                          | (e1,tfun,guard2) ->
                              let c = FStar_Syntax_Syntax.mk_Total tfun  in
                              let uu____9776 =
                                let uu____9781 =
                                  FStar_Syntax_Util.lcomp_of_comp c  in
                                FStar_TypeChecker_Util.strengthen_precondition
                                  FStar_Pervasives_Native.None env1 e1
                                  uu____9781 guard2
                                 in
                              (match uu____9776 with
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
              (let uu____9827 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____9827
               then
                 let uu____9828 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____9829 = FStar_Syntax_Print.term_to_string thead  in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____9828
                   uu____9829
               else ());
              (let monadic_application uu____9900 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____9900 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ
                        in
                     let cres1 =
                       let uu___89_9959 = cres  in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___89_9959.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___89_9959.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp_thunk =
                           (uu___89_9959.FStar_Syntax_Syntax.comp_thunk)
                       }  in
                     let uu____9960 =
                       match bs with
                       | [] ->
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard
                              in
                           (cres1, g)
                       | uu____9974 ->
                           let g =
                             let uu____9982 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard
                                in
                             FStar_All.pipe_right uu____9982
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env)
                              in
                           let uu____9983 =
                             let uu____9984 =
                               let uu____9987 =
                                 let uu____9988 =
                                   FStar_Syntax_Syntax.lcomp_comp cres1  in
                                 FStar_Syntax_Util.arrow bs uu____9988  in
                               FStar_Syntax_Syntax.mk_Total uu____9987  in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____9984
                              in
                           (uu____9983, g)
                        in
                     (match uu____9960 with
                      | (cres2,guard1) ->
                          ((let uu____10002 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low
                               in
                            if uu____10002
                            then
                              let uu____10003 =
                                FStar_Syntax_Print.lcomp_to_string cres2  in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____10003
                            else ());
                           (let cres3 =
                              let head_is_pure_and_some_arg_is_effectful =
                                (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                   chead1)
                                  &&
                                  (FStar_Util.for_some
                                     (fun uu____10019  ->
                                        match uu____10019 with
                                        | (uu____10028,uu____10029,lc) ->
                                            (let uu____10037 =
                                               FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                 lc
                                                in
                                             Prims.op_Negation uu____10037)
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
                              let uu____10047 =
                                (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                   cres2)
                                  && head_is_pure_and_some_arg_is_effectful
                                 in
                              if uu____10047
                              then
                                ((let uu____10049 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme
                                     in
                                  if uu____10049
                                  then
                                    let uu____10050 =
                                      FStar_Syntax_Print.term_to_string term
                                       in
                                    FStar_Util.print1
                                      "(a) Monadic app: Return inserted in monadic application: %s\n"
                                      uu____10050
                                  else ());
                                 FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                   env term cres2)
                              else
                                ((let uu____10054 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme
                                     in
                                  if uu____10054
                                  then
                                    let uu____10055 =
                                      FStar_Syntax_Print.term_to_string term
                                       in
                                    FStar_Util.print1
                                      "(a) Monadic app: No return inserted in monadic application: %s\n"
                                      uu____10055
                                  else ());
                                 cres2)
                               in
                            let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____10079  ->
                                     match uu____10079 with
                                     | ((e,q),x,c) ->
                                         ((let uu____10105 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____10105
                                           then
                                             let uu____10106 =
                                               match x with
                                               | FStar_Pervasives_Native.None
                                                    -> "_"
                                               | FStar_Pervasives_Native.Some
                                                   x1 ->
                                                   FStar_Syntax_Print.bv_to_string
                                                     x1
                                                in
                                             let uu____10108 =
                                               FStar_Syntax_Print.term_to_string
                                                 e
                                                in
                                             FStar_Util.print2
                                               "(b) Monadic app: Binding argument %s : %s\n"
                                               uu____10106 uu____10108
                                           else ());
                                          (let uu____10110 =
                                             FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                               c
                                              in
                                           if uu____10110
                                           then
                                             FStar_TypeChecker_Util.bind
                                               e.FStar_Syntax_Syntax.pos env
                                               (FStar_Pervasives_Native.Some
                                                  e) c (x, out_c)
                                           else
                                             FStar_TypeChecker_Util.bind
                                               e.FStar_Syntax_Syntax.pos env
                                               FStar_Pervasives_Native.None c
                                               (x, out_c)))) cres3
                                arg_comps_rev
                               in
                            let comp1 =
                              (let uu____10118 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme
                                  in
                               if uu____10118
                               then
                                 let uu____10119 =
                                   FStar_Syntax_Print.term_to_string head2
                                    in
                                 FStar_Util.print1
                                   "(c) Monadic app: Binding head %s "
                                   uu____10119
                               else ());
                              (let uu____10121 =
                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                   chead1
                                  in
                               if uu____10121
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
                              FStar_TypeChecker_Util.subst_lcomp subst1 comp1
                               in
                            let shortcuts_evaluation_order =
                              let uu____10129 =
                                let uu____10130 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____10130.FStar_Syntax_Syntax.n  in
                              match uu____10129 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____10134 -> false  in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____10155  ->
                                         match uu____10155 with
                                         | (arg,uu____10169,uu____10170) ->
                                             arg :: args1) [] arg_comps_rev
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
                                (let uu____10180 =
                                   let map_fun uu____10244 =
                                     match uu____10244 with
                                     | ((e,q),uu____10279,c) ->
                                         let uu____10289 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c
                                            in
                                         if uu____10289
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
                                            let uu____10339 =
                                              let uu____10344 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              (uu____10344, q)  in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____10339))
                                      in
                                   let uu____10373 =
                                     let uu____10398 =
                                       let uu____10421 =
                                         let uu____10436 =
                                           let uu____10445 =
                                             FStar_Syntax_Syntax.as_arg head2
                                              in
                                           (uu____10445,
                                             FStar_Pervasives_Native.None,
                                             chead1)
                                            in
                                         uu____10436 :: arg_comps_rev  in
                                       FStar_List.map map_fun uu____10421  in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____10398
                                      in
                                   match uu____10373 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____10618 =
                                         let uu____10619 =
                                           FStar_List.hd reverse_args  in
                                         FStar_Pervasives_Native.fst
                                           uu____10619
                                          in
                                       let uu____10628 =
                                         let uu____10635 =
                                           FStar_List.tl reverse_args  in
                                         FStar_List.rev uu____10635  in
                                       (lifted_args, uu____10618,
                                         uu____10628)
                                    in
                                 match uu____10180 with
                                 | (lifted_args,head3,args1) ->
                                     let app =
                                       FStar_Syntax_Syntax.mk_Tm_app head3
                                         args1 FStar_Pervasives_Native.None r
                                        in
                                     let app1 =
                                       FStar_TypeChecker_Util.maybe_lift env
                                         app
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
                                     let bind_lifted_args e uu___67_10742 =
                                       match uu___67_10742 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1
                                               [] e1.FStar_Syntax_Syntax.pos
                                              in
                                           let letbinding =
                                             let uu____10799 =
                                               let uu____10806 =
                                                 let uu____10807 =
                                                   let uu____10820 =
                                                     let uu____10821 =
                                                       let uu____10822 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x
                                                          in
                                                       [uu____10822]  in
                                                     FStar_Syntax_Subst.close
                                                       uu____10821 e
                                                      in
                                                   ((false, [lb]),
                                                     uu____10820)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____10807
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10806
                                                in
                                             uu____10799
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
                                     FStar_List.fold_left bind_lifted_args
                                       app2 lifted_args)
                               in
                            let uu____10852 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp2
                                guard1
                               in
                            match uu____10852 with
                            | (comp3,g) ->
                                ((let uu____10869 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme
                                     in
                                  if uu____10869
                                  then
                                    let uu____10870 =
                                      FStar_Syntax_Print.term_to_string app
                                       in
                                    let uu____10871 =
                                      FStar_Syntax_Print.lcomp_to_string
                                        comp3
                                       in
                                    FStar_Util.print2
                                      "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                      uu____10870 uu____10871
                                  else ());
                                 (app, comp3, g)))))
                  in
               let rec tc_args head_info uu____10955 bs args1 =
                 match uu____10955 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____11098))::rest,
                         (uu____11100,FStar_Pervasives_Native.None )::uu____11101)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          let uu____11152 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____11152 with
                           | (varg,uu____11172,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1
                                  in
                               let arg =
                                 let uu____11194 =
                                   FStar_Syntax_Syntax.as_implicit true  in
                                 (varg, uu____11194)  in
                               let uu____11195 =
                                 let uu____11230 =
                                   let uu____11245 =
                                     let uu____11258 =
                                       let uu____11259 =
                                         FStar_Syntax_Syntax.mk_Total t1  in
                                       FStar_All.pipe_right uu____11259
                                         FStar_Syntax_Util.lcomp_of_comp
                                        in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____11258)
                                      in
                                   uu____11245 :: outargs  in
                                 let uu____11278 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g
                                    in
                                 (subst2, uu____11230, (arg :: arg_rets),
                                   uu____11278, fvs)
                                  in
                               tc_args head_info uu____11195 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____11370),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11371)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____11384 ->
                                let uu____11393 =
                                  let uu____11398 =
                                    let uu____11399 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____11400 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____11401 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____11402 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____11399 uu____11400 uu____11401
                                      uu____11402
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____11398)
                                   in
                                FStar_Errors.raise_error uu____11393
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x1 =
                              let uu___90_11405 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___90_11405.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___90_11405.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____11407 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____11407
                             then
                               let uu____11408 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____11408
                             else ());
                            (let targ1 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ
                                in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1
                                in
                             let env2 =
                               let uu___91_11413 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___91_11413.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___91_11413.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___91_11413.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___91_11413.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___91_11413.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___91_11413.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___91_11413.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___91_11413.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___91_11413.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___91_11413.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___91_11413.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___91_11413.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___91_11413.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___91_11413.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___91_11413.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___91_11413.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___91_11413.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___91_11413.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___91_11413.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___91_11413.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___91_11413.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___91_11413.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___91_11413.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___91_11413.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___91_11413.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___91_11413.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___91_11413.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___91_11413.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___91_11413.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___91_11413.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___91_11413.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___91_11413.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___91_11413.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___91_11413.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___91_11413.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___91_11413.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             (let uu____11415 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High
                                 in
                              if uu____11415
                              then
                                let uu____11416 =
                                  FStar_Syntax_Print.tag_of_term e  in
                                let uu____11417 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____11418 =
                                  FStar_Syntax_Print.term_to_string targ1  in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____11416 uu____11417 uu____11418
                              else ());
                             (let uu____11420 = tc_term env2 e  in
                              match uu____11420 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e
                                     in
                                  let arg = (e1, aq)  in
                                  let xterm =
                                    let uu____11455 =
                                      let uu____11458 =
                                        let uu____11465 =
                                          FStar_Syntax_Syntax.bv_to_name x1
                                           in
                                        FStar_Syntax_Syntax.as_arg
                                          uu____11465
                                         in
                                      FStar_Pervasives_Native.fst uu____11458
                                       in
                                    (uu____11455, aq)  in
                                  let uu____11472 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name)
                                     in
                                  if uu____11472
                                  then
                                    let subst2 =
                                      let uu____11480 = FStar_List.hd bs  in
                                      maybe_extend_subst subst1 uu____11480
                                        e1
                                       in
                                    tc_args head_info
                                      (subst2,
                                        ((arg,
                                           (FStar_Pervasives_Native.Some x1),
                                           c) :: outargs), (xterm ::
                                        arg_rets), g1, fvs) rest rest'
                                  else
                                    tc_args head_info
                                      (subst1,
                                        ((arg,
                                           (FStar_Pervasives_Native.Some x1),
                                           c) :: outargs), (xterm ::
                                        arg_rets), g1, (x1 :: fvs)) rest
                                      rest'))))
                      | (uu____11606,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____11638) ->
                          let uu____11681 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____11681 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____11719 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____11719
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____11744 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____11744 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            let uu____11766 =
                                              FStar_Syntax_Util.lcomp_of_comp
                                                cres'1
                                               in
                                            (head2, chead1, ghead1,
                                              uu____11766)
                                             in
                                          ((let uu____11768 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____11768
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
                                 | uu____11810 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2
                                          in
                                       let uu____11818 =
                                         let uu____11819 =
                                           FStar_Syntax_Subst.compress tres3
                                            in
                                         uu____11819.FStar_Syntax_Syntax.n
                                          in
                                       match uu____11818 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____11822;
                                              FStar_Syntax_Syntax.index =
                                                uu____11823;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},uu____11825)
                                           -> norm_tres tres4
                                       | uu____11832 -> tres3  in
                                     let uu____11833 = norm_tres tres1  in
                                     aux true uu____11833
                                 | uu____11834 ->
                                     let uu____11835 =
                                       let uu____11840 =
                                         let uu____11841 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead
                                            in
                                         let uu____11842 =
                                           FStar_Util.string_of_int n_args
                                            in
                                         FStar_Util.format2
                                           "Too many arguments to function of type %s; got %s arguments"
                                           uu____11841 uu____11842
                                          in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____11840)
                                        in
                                     let uu____11849 =
                                       FStar_Syntax_Syntax.argpos arg  in
                                     FStar_Errors.raise_error uu____11835
                                       uu____11849
                                  in
                               aux false chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app tf =
                 let uu____11868 =
                   let uu____11869 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____11869.FStar_Syntax_Syntax.n  in
                 match uu____11868 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____11878 ->
                     let bs =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun uu____11916  ->
                               let uu____11923 =
                                 let uu____11924 =
                                   let uu____11925 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_right uu____11925
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_TypeChecker_Util.new_uvar env
                                   uu____11924
                                  in
                               FStar_Syntax_Syntax.null_binder uu____11923))
                        in
                     let cres =
                       let t =
                         let uu____11936 =
                           let uu____11937 = FStar_Syntax_Util.type_u ()  in
                           FStar_All.pipe_right uu____11937
                             FStar_Pervasives_Native.fst
                            in
                         FStar_TypeChecker_Util.new_uvar env uu____11936  in
                       let uu____11946 = FStar_Options.ml_ish ()  in
                       if uu____11946
                       then FStar_Syntax_Util.ml_comp t r
                       else FStar_Syntax_Syntax.mk_Total t  in
                     let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                     ((let uu____11952 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           FStar_Options.Extreme
                          in
                       if uu____11952
                       then
                         let uu____11953 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____11954 =
                           FStar_Syntax_Print.term_to_string tf  in
                         let uu____11955 =
                           FStar_Syntax_Print.term_to_string bs_cres  in
                         FStar_Util.print3
                           "Forcing the type of %s from %s to %s\n"
                           uu____11953 uu____11954 uu____11955
                       else ());
                      (let uu____11958 =
                         FStar_TypeChecker_Rel.teq env tf bs_cres  in
                       FStar_All.pipe_left
                         (FStar_TypeChecker_Rel.force_trivial_guard env)
                         uu____11958);
                      check_function_app bs_cres)
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____11959;
                        FStar_Syntax_Syntax.pos = uu____11960;
                        FStar_Syntax_Syntax.vars = uu____11961;_},uu____11962)
                     ->
                     let bs =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun uu____12020  ->
                               let uu____12027 =
                                 let uu____12028 =
                                   let uu____12029 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_right uu____12029
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_TypeChecker_Util.new_uvar env
                                   uu____12028
                                  in
                               FStar_Syntax_Syntax.null_binder uu____12027))
                        in
                     let cres =
                       let t =
                         let uu____12040 =
                           let uu____12041 = FStar_Syntax_Util.type_u ()  in
                           FStar_All.pipe_right uu____12041
                             FStar_Pervasives_Native.fst
                            in
                         FStar_TypeChecker_Util.new_uvar env uu____12040  in
                       let uu____12050 = FStar_Options.ml_ish ()  in
                       if uu____12050
                       then FStar_Syntax_Util.ml_comp t r
                       else FStar_Syntax_Syntax.mk_Total t  in
                     let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                     ((let uu____12056 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           FStar_Options.Extreme
                          in
                       if uu____12056
                       then
                         let uu____12057 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____12058 =
                           FStar_Syntax_Print.term_to_string tf  in
                         let uu____12059 =
                           FStar_Syntax_Print.term_to_string bs_cres  in
                         FStar_Util.print3
                           "Forcing the type of %s from %s to %s\n"
                           uu____12057 uu____12058 uu____12059
                       else ());
                      (let uu____12062 =
                         FStar_TypeChecker_Rel.teq env tf bs_cres  in
                       FStar_All.pipe_left
                         (FStar_TypeChecker_Rel.force_trivial_guard env)
                         uu____12062);
                      check_function_app bs_cres)
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____12081 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____12081 with
                      | (bs1,c1) ->
                          let head_info =
                            let uu____12103 =
                              FStar_Syntax_Util.lcomp_of_comp c1  in
                            (head1, chead, ghead, uu____12103)  in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____12145) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____12151,uu____12152) -> check_function_app t
                 | uu____12193 ->
                     let uu____12194 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____12194
                       head1.FStar_Syntax_Syntax.pos
                  in
               check_function_app thead)

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
                  let uu____12266 =
                    FStar_List.fold_left2
                      (fun uu____12309  ->
                         fun uu____12310  ->
                           fun uu____12311  ->
                             match (uu____12309, uu____12310, uu____12311)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                        "Inconsistent implicit qualifiers")
                                      e.FStar_Syntax_Syntax.pos
                                  else ();
                                  (let uu____12379 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____12379 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____12397 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____12397 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____12401 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____12401)
                                              &&
                                              (let uu____12403 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____12403))
                                          in
                                       let uu____12404 =
                                         let uu____12413 =
                                           let uu____12422 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____12422]  in
                                         FStar_List.append seen uu____12413
                                          in
                                       let uu____12429 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1
                                          in
                                       (uu____12404, uu____12429, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____12266 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____12465 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____12465
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____12467 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____12467 with | (c2,g) -> (e, c2, g)))
              | uu____12485 ->
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
        let uu____12528 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____12528 with
        | (pattern,when_clause,branch_exp) ->
            let uu____12573 = branch1  in
            (match uu____12573 with
             | (cpat,uu____12614,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let tc_annot env1 t =
                     let uu____12691 = FStar_Syntax_Util.type_u ()  in
                     match uu____12691 with
                     | (tu,u) ->
                         let uu____12702 =
                           tc_check_tot_or_gtot_term env1 t tu  in
                         (match uu____12702 with
                          | (t1,uu____12714,g) -> (t1, g))
                      in
                   let uu____12716 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0
                       tc_annot
                      in
                   match uu____12716 with
                   | (pat_bvs1,exp,guard_pat_annots,p) ->
                       ((let uu____12750 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         if uu____12750
                         then
                           let uu____12751 =
                             FStar_Syntax_Print.pat_to_string p0  in
                           let uu____12752 =
                             FStar_Syntax_Print.pat_to_string p  in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____12751 uu____12752
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1
                            in
                         let uu____12755 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env
                            in
                         match uu____12755 with
                         | (env1,uu____12777) ->
                             let env11 =
                               let uu___92_12783 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___92_12783.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___92_12783.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___92_12783.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___92_12783.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___92_12783.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___92_12783.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___92_12783.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___92_12783.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___92_12783.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___92_12783.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___92_12783.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___92_12783.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___92_12783.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___92_12783.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___92_12783.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___92_12783.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___92_12783.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___92_12783.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___92_12783.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___92_12783.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___92_12783.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___92_12783.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___92_12783.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___92_12783.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___92_12783.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___92_12783.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___92_12783.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___92_12783.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___92_12783.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___92_12783.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___92_12783.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___92_12783.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___92_12783.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___92_12783.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___92_12783.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___92_12783.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t  in
                             ((let uu____12786 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High
                                  in
                               if uu____12786
                               then
                                 let uu____12787 =
                                   FStar_Syntax_Print.term_to_string exp  in
                                 let uu____12788 =
                                   FStar_Syntax_Print.term_to_string pat_t
                                    in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____12787 uu____12788
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t
                                  in
                               let uu____12791 =
                                 tc_tot_or_gtot_term env12 exp  in
                               match uu____12791 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___93_12816 = g  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___93_12816.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___93_12816.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___93_12816.FStar_TypeChecker_Env.implicits)
                                     }  in
                                   let uu____12817 =
                                     let uu____12818 =
                                       FStar_TypeChecker_Rel.teq_nosmt env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t
                                        in
                                     if uu____12818
                                     then
                                       let env13 =
                                         FStar_TypeChecker_Env.set_range
                                           env12 exp1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____12820 =
                                         FStar_TypeChecker_Rel.discharge_guard_no_smt
                                           env13 g1
                                          in
                                       FStar_All.pipe_right uu____12820
                                         FStar_TypeChecker_Rel.resolve_implicits
                                     else
                                       (let uu____12822 =
                                          let uu____12827 =
                                            let uu____12828 =
                                              FStar_Syntax_Print.term_to_string
                                                lc.FStar_Syntax_Syntax.res_typ
                                               in
                                            let uu____12829 =
                                              FStar_Syntax_Print.term_to_string
                                                expected_pat_t
                                               in
                                            FStar_Util.format2
                                              "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                              uu____12828 uu____12829
                                             in
                                          (FStar_Errors.Fatal_MismatchedPatternType,
                                            uu____12827)
                                           in
                                        FStar_Errors.raise_error uu____12822
                                          exp1.FStar_Syntax_Syntax.pos)
                                      in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1
                                      in
                                   let uvs_to_string uvs =
                                     let uu____12849 =
                                       let uu____12852 =
                                         FStar_Util.set_elements uvs  in
                                       FStar_All.pipe_right uu____12852
                                         (FStar_List.map
                                            (fun uu____12878  ->
                                               match uu____12878 with
                                               | (u,uu____12884) ->
                                                   FStar_Syntax_Print.uvar_to_string
                                                     u))
                                        in
                                     FStar_All.pipe_right uu____12849
                                       (FStar_String.concat ", ")
                                      in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp  in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t
                                      in
                                   ((let uu____12902 =
                                       FStar_TypeChecker_Env.debug env
                                         (FStar_Options.Other "Free")
                                        in
                                     if uu____12902
                                     then
                                       ((let uu____12904 =
                                           FStar_Syntax_Print.term_to_string
                                             norm_exp
                                            in
                                         let uu____12905 = uvs_to_string uvs1
                                            in
                                         FStar_Util.print2
                                           ">> free_1(%s) = %s\n" uu____12904
                                           uu____12905);
                                        (let uu____12906 =
                                           FStar_Syntax_Print.term_to_string
                                             expected_pat_t
                                            in
                                         let uu____12907 = uvs_to_string uvs2
                                            in
                                         FStar_Util.print2
                                           ">> free_2(%s) = %s\n" uu____12906
                                           uu____12907))
                                     else ());
                                    (let uu____12910 =
                                       let uu____12911 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2
                                          in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____12911
                                        in
                                     if uu____12910
                                     then
                                       let unresolved =
                                         FStar_Util.set_difference uvs1 uvs2
                                          in
                                       let uu____12927 =
                                         let uu____12932 =
                                           let uu____12933 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env norm_exp
                                              in
                                           let uu____12934 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env expected_pat_t
                                              in
                                           let uu____12935 =
                                             uvs_to_string unresolved  in
                                           FStar_Util.format3
                                             "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                             uu____12933 uu____12934
                                             uu____12935
                                            in
                                         (FStar_Errors.Fatal_UnresolvedPatternVar,
                                           uu____12932)
                                          in
                                       FStar_Errors.raise_error uu____12927
                                         p.FStar_Syntax_Syntax.p
                                     else ());
                                    (let uu____12938 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High
                                        in
                                     if uu____12938
                                     then
                                       let uu____12939 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1
                                          in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____12939
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
                 let uu____12948 =
                   let uu____12955 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____12955
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____12948 with
                  | (scrutinee_env,uu____12988) ->
                      let uu____12993 = tc_pat true pat_t pattern  in
                      (match uu____12993 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,guard_pat_annots,norm_pat_exp)
                           ->
                           let uu____13043 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____13065 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____13065
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____13079 =
                                      let uu____13086 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____13086 e  in
                                    match uu____13079 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____13043 with
                            | (when_clause1,g_when) ->
                                let uu____13129 = tc_term pat_env branch_exp
                                   in
                                (match uu____13129 with
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
                                           let uu____13171 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_18  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_18) uu____13171
                                        in
                                     let uu____13174 =
                                       let eqs =
                                         let uu____13193 =
                                           let uu____13194 =
                                             FStar_TypeChecker_Env.should_verify
                                               env
                                              in
                                           Prims.op_Negation uu____13194  in
                                         if uu____13193
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp
                                               in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____13201 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____13218 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____13219 ->
                                                FStar_Pervasives_Native.None
                                            | uu____13220 ->
                                                let uu____13221 =
                                                  let uu____13222 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____13222 pat_t
                                                    scrutinee_tm e
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____13221)
                                          in
                                       let uu____13223 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch1
                                          in
                                       match uu____13223 with
                                       | (c1,g_branch2) ->
                                           let uu____13248 =
                                             match (eqs, when_condition) with
                                             | uu____13261 when
                                                 let uu____13270 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation
                                                   uu____13270
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
                                                 let uu____13282 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf
                                                    in
                                                 let uu____13283 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when
                                                    in
                                                 (uu____13282, uu____13283)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g_fw =
                                                   let uu____13292 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w
                                                      in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____13292
                                                    in
                                                 let uu____13293 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw
                                                    in
                                                 let uu____13294 =
                                                   let uu____13295 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f
                                                      in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____13295 g_when
                                                    in
                                                 (uu____13293, uu____13294)
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
                                                 let uu____13303 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w
                                                    in
                                                 (uu____13303, g_when)
                                              in
                                           (match uu____13248 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1
                                                   in
                                                let maybe_return_c_weak
                                                  should_return =
                                                  let c_weak1 =
                                                    let uu____13331 =
                                                      should_return &&
                                                        (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                           c_weak)
                                                       in
                                                    if uu____13331
                                                    then
                                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                        env branch_exp1
                                                        c_weak
                                                    else c_weak  in
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak1
                                                   in
                                                let uu____13333 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak
                                                   in
                                                ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                  (c_weak.FStar_Syntax_Syntax.cflags),
                                                  maybe_return_c_weak,
                                                  uu____13333, g_branch2))
                                        in
                                     (match uu____13174 with
                                      | (effect_label,cflags,maybe_return_c,g_when1,g_branch2)
                                          ->
                                          let branch_guard =
                                            let uu____13380 =
                                              let uu____13381 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____13381
                                               in
                                            if uu____13380
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____13419 =
                                                     let uu____13420 =
                                                       let uu____13421 =
                                                         let uu____13424 =
                                                           let uu____13431 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v
                                                              in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____13431
                                                            in
                                                         FStar_Pervasives_Native.snd
                                                           uu____13424
                                                          in
                                                       FStar_List.length
                                                         uu____13421
                                                        in
                                                     uu____13420 >
                                                       (Prims.parse_int "1")
                                                      in
                                                   if uu____13419
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     let uu____13437 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator
                                                        in
                                                     match uu____13437 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____13458 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         let disc1 =
                                                           let uu____13473 =
                                                             let uu____13478
                                                               =
                                                               let uu____13479
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2
                                                                  in
                                                               [uu____13479]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____13478
                                                              in
                                                           uu____13473
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                            in
                                                         let uu____13482 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool
                                                            in
                                                         [uu____13482]
                                                   else []  in
                                                 let fail1 uu____13489 =
                                                   let uu____13490 =
                                                     let uu____13491 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos
                                                        in
                                                     let uu____13492 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1
                                                        in
                                                     let uu____13493 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1
                                                        in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____13491
                                                       uu____13492
                                                       uu____13493
                                                      in
                                                   failwith uu____13490  in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____13506) ->
                                                       head_constructor t1
                                                   | uu____13511 -> fail1 ()
                                                    in
                                                 let pat_exp2 =
                                                   let uu____13513 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____13513
                                                     FStar_Syntax_Util.unmeta
                                                    in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____13516 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____13533;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____13534;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____13535;_},uu____13536)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____13573 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c1 ->
                                                     let uu____13575 =
                                                       let uu____13576 =
                                                         tc_constant env
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c1
                                                          in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____13576
                                                         scrutinee_tm1
                                                         pat_exp2
                                                        in
                                                     [uu____13575]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____13577 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____13585 =
                                                       let uu____13586 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____13586
                                                        in
                                                     if uu____13585
                                                     then []
                                                     else
                                                       (let uu____13590 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13590)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____13593 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____13595 =
                                                       let uu____13596 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____13596
                                                        in
                                                     if uu____13595
                                                     then []
                                                     else
                                                       (let uu____13600 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13600)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1
                                                        in
                                                     let uu____13626 =
                                                       let uu____13627 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____13627
                                                        in
                                                     if uu____13626
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____13634 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____13666
                                                                     ->
                                                                    match uu____13666
                                                                    with
                                                                    | 
                                                                    (ei,uu____13676)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____13682
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____13682
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____13703
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____13717
                                                                    =
                                                                    let uu____13722
                                                                    =
                                                                    let uu____13723
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____13723
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____13724
                                                                    =
                                                                    let uu____13725
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1
                                                                     in
                                                                    [uu____13725]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____13722
                                                                    uu____13724
                                                                     in
                                                                    uu____13717
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13634
                                                            FStar_List.flatten
                                                           in
                                                        let uu____13734 =
                                                          discriminate
                                                            scrutinee_tm1 f
                                                           in
                                                        FStar_List.append
                                                          uu____13734
                                                          sub_term_guards)
                                                 | uu____13737 -> []  in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____13753 =
                                                   let uu____13754 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____13754
                                                    in
                                                 if uu____13753
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____13757 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____13757
                                                       in
                                                    let uu____13762 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    match uu____13762 with
                                                    | (k,uu____13768) ->
                                                        let uu____13769 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k
                                                           in
                                                        (match uu____13769
                                                         with
                                                         | (t1,uu____13777,uu____13778)
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
                                          ((let uu____13784 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High
                                               in
                                            if uu____13784
                                            then
                                              let uu____13785 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard
                                                 in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____13785
                                            else ());
                                           (let uu____13787 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1)
                                               in
                                            (uu____13787, branch_guard,
                                              effect_label, cflags,
                                              maybe_return_c, guard)))))))))

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
          let uu____13818 = check_let_bound_def true env1 lb  in
          (match uu____13818 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____13840 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____13857 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____13857, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____13860 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____13860
                        FStar_TypeChecker_Rel.resolve_implicits
                       in
                    let uu____13862 =
                      let uu____13875 =
                        let uu____13890 =
                          let uu____13899 =
                            let uu____13910 =
                              FStar_Syntax_Syntax.lcomp_comp c1  in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____13910)
                             in
                          [uu____13899]  in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____13890
                         in
                      FStar_List.hd uu____13875  in
                    match uu____13862 with
                    | (uu____13955,univs1,e11,c11,gvs) ->
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
                        let uu____13969 = FStar_Syntax_Util.lcomp_of_comp c11
                           in
                        (g13, e11, univs1, uu____13969))
                  in
               (match uu____13840 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____13980 =
                      let uu____13987 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____13987
                      then
                        let uu____13994 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____13994 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____14017 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____14017
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____14018 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____14018, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____14028 =
                              FStar_Syntax_Syntax.lcomp_comp c11  in
                            FStar_All.pipe_right uu____14028
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm;
                                 FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]
                                 env1)
                             in
                          let e21 =
                            let uu____14032 =
                              FStar_Syntax_Util.is_pure_comp c  in
                            if uu____14032
                            then e2
                            else
                              ((let uu____14037 =
                                  FStar_TypeChecker_Env.get_range env1  in
                                FStar_Errors.log_issue uu____14037
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
                    (match uu____13980 with
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
                         let uu____14058 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos
                            in
                         let uu____14071 =
                           FStar_Syntax_Util.lcomp_of_comp cres  in
                         (uu____14058, uu____14071,
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____14074 -> failwith "Impossible"

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
            let uu___94_14105 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___94_14105.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___94_14105.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___94_14105.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___94_14105.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___94_14105.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___94_14105.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___94_14105.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___94_14105.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___94_14105.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___94_14105.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___94_14105.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___94_14105.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___94_14105.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___94_14105.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___94_14105.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___94_14105.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___94_14105.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___94_14105.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___94_14105.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___94_14105.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___94_14105.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___94_14105.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___94_14105.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___94_14105.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___94_14105.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___94_14105.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___94_14105.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___94_14105.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___94_14105.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___94_14105.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___94_14105.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___94_14105.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___94_14105.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___94_14105.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___94_14105.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___94_14105.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____14106 =
            let uu____14117 =
              let uu____14118 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____14118 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____14117 lb  in
          (match uu____14106 with
           | (e1,uu____14140,c1,g1,annotated) ->
               ((let uu____14145 =
                   (FStar_Util.for_some
                      (FStar_Syntax_Util.is_fvar
                         FStar_Parser_Const.inline_let_attr)
                      lb.FStar_Syntax_Syntax.lbattrs)
                     &&
                     (let uu____14147 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp c1  in
                      Prims.op_Negation uu____14147)
                    in
                 if uu____14145
                 then
                   let uu____14148 =
                     let uu____14153 =
                       let uu____14154 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____14155 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____14154 uu____14155
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____14153)
                      in
                   FStar_Errors.raise_error uu____14148
                     e1.FStar_Syntax_Syntax.pos
                 else ());
                (let x =
                   let uu___95_14158 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___95_14158.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___95_14158.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_Syntax_Syntax.res_typ)
                   }  in
                 let uu____14159 =
                   let uu____14164 =
                     let uu____14165 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____14165]  in
                   FStar_Syntax_Subst.open_term uu____14164 e2  in
                 match uu____14159 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____14185 = tc_term env_x e21  in
                     (match uu____14185 with
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
                            let uu____14210 =
                              let uu____14217 =
                                let uu____14218 =
                                  let uu____14231 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____14231)  in
                                FStar_Syntax_Syntax.Tm_let uu____14218  in
                              FStar_Syntax_Syntax.mk uu____14217  in
                            uu____14210 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.res_typ
                             in
                          let x_eq_e1 =
                            let uu____14245 =
                              let uu____14246 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_Syntax_Syntax.res_typ
                                 in
                              let uu____14247 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____14246
                                c1.FStar_Syntax_Syntax.res_typ uu____14247
                                e11
                               in
                            FStar_All.pipe_left
                              (fun _0_19  ->
                                 FStar_TypeChecker_Common.NonTrivial _0_19)
                              uu____14245
                             in
                          let g21 =
                            let uu____14249 =
                              let uu____14250 =
                                FStar_TypeChecker_Rel.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Rel.imp_guard uu____14250 g2
                               in
                            FStar_TypeChecker_Rel.close_guard env2 xb
                              uu____14249
                             in
                          let guard = FStar_TypeChecker_Rel.conj_guard g1 g21
                             in
                          let uu____14252 =
                            let uu____14253 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____14253  in
                          if uu____14252
                          then
                            let tt =
                              let uu____14263 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____14263
                                FStar_Option.get
                               in
                            ((let uu____14269 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____14269
                              then
                                let uu____14270 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____14271 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____14270 uu____14271
                              else ());
                             (e4, cres, guard))
                          else
                            (let t =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1] cres.FStar_Syntax_Syntax.res_typ
                                in
                             (let uu____14276 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____14276
                              then
                                let uu____14277 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____14278 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "Checked %s has no escaping types; normalized to %s\n"
                                  uu____14277 uu____14278
                              else ());
                             (e4,
                               ((let uu___96_14281 = cres  in
                                 {
                                   FStar_Syntax_Syntax.eff_name =
                                     (uu___96_14281.FStar_Syntax_Syntax.eff_name);
                                   FStar_Syntax_Syntax.res_typ = t;
                                   FStar_Syntax_Syntax.cflags =
                                     (uu___96_14281.FStar_Syntax_Syntax.cflags);
                                   FStar_Syntax_Syntax.comp_thunk =
                                     (uu___96_14281.FStar_Syntax_Syntax.comp_thunk)
                                 })), guard))))))
      | uu____14282 -> failwith "Impossible"

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
          let uu____14314 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____14314 with
           | (lbs1,e21) ->
               let uu____14333 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____14333 with
                | (env0,topt) ->
                    let uu____14352 = build_let_rec_env true env0 lbs1  in
                    (match uu____14352 with
                     | (lbs2,rec_env) ->
                         let uu____14371 = check_let_recs rec_env lbs2  in
                         (match uu____14371 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____14391 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs
                                   in
                                FStar_All.pipe_right uu____14391
                                  FStar_TypeChecker_Rel.resolve_implicits
                                 in
                              let all_lb_names =
                                let uu____14397 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____14397
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
                                     let uu____14446 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____14486 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____14486)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____14446
                                      in
                                   FStar_List.map2
                                     (fun uu____14520  ->
                                        fun lb  ->
                                          match uu____14520 with
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
                                let uu____14568 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____14568
                                 in
                              let uu____14573 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____14573 with
                               | (lbs5,e22) ->
                                   ((let uu____14593 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____14593
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____14594 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____14594, cres,
                                       FStar_TypeChecker_Rel.trivial_guard))))))))
      | uu____14607 -> failwith "Impossible"

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
          let uu____14639 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____14639 with
           | (lbs1,e21) ->
               let uu____14658 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____14658 with
                | (env0,topt) ->
                    let uu____14677 = build_let_rec_env false env0 lbs1  in
                    (match uu____14677 with
                     | (lbs2,rec_env) ->
                         let uu____14696 = check_let_recs rec_env lbs2  in
                         (match uu____14696 with
                          | (lbs3,g_lbs) ->
                              let uu____14715 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___97_14738 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___97_14738.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___97_14738.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___98_14740 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___98_14740.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___98_14740.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___98_14740.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___98_14740.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___98_14740.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___98_14740.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____14715 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____14767 = tc_term env2 e21  in
                                   (match uu____14767 with
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
                                          let uu____14786 =
                                            let uu____14787 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____14787 g2
                                             in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____14786
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
                                          let uu___99_14791 = cres3  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___99_14791.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___99_14791.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___99_14791.FStar_Syntax_Syntax.comp_thunk)
                                          }  in
                                        let uu____14792 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____14792 with
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
                                                  uu____14828 ->
                                                  (e, cres4, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  let cres5 =
                                                    let uu___100_14833 =
                                                      cres4  in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___100_14833.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___100_14833.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp_thunk
                                                        =
                                                        (uu___100_14833.FStar_Syntax_Syntax.comp_thunk)
                                                    }  in
                                                  (e, cres5, guard)))))))))
      | uu____14836 -> failwith "Impossible"

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
          let uu____14871 = FStar_Options.ml_ish ()  in
          if uu____14871
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____14874 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____14874 with
             | (formals,c) ->
                 let uu____14899 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____14899 with
                  | (actuals,uu____14909,uu____14910) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____14923 =
                          let uu____14928 =
                            let uu____14929 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____14930 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____14929 uu____14930
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____14928)
                           in
                        FStar_Errors.raise_error uu____14923
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____14933 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____14933 actuals
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
                                (let uu____14954 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____14954)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____14972 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____14972)
                               in
                            let msg =
                              let uu____14980 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____14981 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____14980 uu____14981 formals_msg
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
        let uu____14988 =
          FStar_List.fold_left
            (fun uu____15014  ->
               fun lb  ->
                 match uu____15014 with
                 | (lbs1,env1) ->
                     let uu____15034 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____15034 with
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
                               let uu____15055 =
                                 let uu____15062 =
                                   let uu____15063 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____15063
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___101_15074 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___101_15074.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___101_15074.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___101_15074.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___101_15074.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___101_15074.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___101_15074.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___101_15074.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___101_15074.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___101_15074.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___101_15074.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___101_15074.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___101_15074.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___101_15074.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___101_15074.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___101_15074.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___101_15074.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___101_15074.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___101_15074.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___101_15074.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___101_15074.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___101_15074.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___101_15074.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___101_15074.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___101_15074.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___101_15074.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___101_15074.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___101_15074.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___101_15074.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___101_15074.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___101_15074.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___101_15074.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___101_15074.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___101_15074.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___101_15074.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___101_15074.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___101_15074.FStar_TypeChecker_Env.dep_graph)
                                    }) t uu____15062
                                  in
                               match uu____15055 with
                               | (t1,uu____15076,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g
                                      in
                                   ((let uu____15080 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1
                                        in
                                     FStar_All.pipe_left (fun a238  -> ())
                                       uu____15080);
                                    norm env01 t1))
                             in
                          let env3 =
                            let uu____15082 =
                              termination_check_enabled
                                lb.FStar_Syntax_Syntax.lbname e t1
                               in
                            if uu____15082
                            then
                              let uu___102_15083 = env2  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___102_15083.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___102_15083.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___102_15083.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___102_15083.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___102_15083.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___102_15083.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___102_15083.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___102_15083.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___102_15083.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___102_15083.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___102_15083.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___102_15083.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1,
                                     univ_vars1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___102_15083.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___102_15083.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___102_15083.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___102_15083.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___102_15083.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___102_15083.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___102_15083.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___102_15083.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___102_15083.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___102_15083.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___102_15083.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___102_15083.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___102_15083.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___102_15083.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___102_15083.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___102_15083.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___102_15083.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___102_15083.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___102_15083.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___102_15083.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___102_15083.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___102_15083.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___102_15083.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___102_15083.FStar_TypeChecker_Env.dep_graph)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname
                                (univ_vars1, t1)
                             in
                          let lb1 =
                            let uu___103_15100 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___103_15100.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___103_15100.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___103_15100.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___103_15100.FStar_Syntax_Syntax.lbpos)
                            }  in
                          ((lb1 :: lbs1), env3))) ([], env) lbs
           in
        match uu____14988 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lbs  ->
      let uu____15123 =
        let uu____15132 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____15158 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____15158 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____15186 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____15186
                       | uu____15191 ->
                           let lb1 =
                             let uu___104_15194 = lb  in
                             let uu____15195 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___104_15194.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___104_15194.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___104_15194.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___104_15194.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____15195;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___104_15194.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___104_15194.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____15198 =
                             let uu____15205 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____15205
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____15198 with
                            | (e,c,g) ->
                                ((let uu____15214 =
                                    let uu____15215 =
                                      FStar_Syntax_Util.is_total_lcomp c  in
                                    Prims.op_Negation uu____15215  in
                                  if uu____15214
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
        FStar_All.pipe_right uu____15132 FStar_List.unzip  in
      match uu____15123 with
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
        let uu____15264 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____15264 with
        | (env1,uu____15282) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____15290 = check_lbtyp top_level env lb  in
            (match uu____15290 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____15332 =
                     tc_maybe_toplevel_term
                       (let uu___105_15341 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___105_15341.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___105_15341.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___105_15341.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___105_15341.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___105_15341.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___105_15341.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___105_15341.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___105_15341.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___105_15341.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___105_15341.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___105_15341.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___105_15341.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___105_15341.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___105_15341.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___105_15341.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___105_15341.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___105_15341.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___105_15341.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___105_15341.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.failhard =
                            (uu___105_15341.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___105_15341.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___105_15341.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___105_15341.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___105_15341.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___105_15341.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___105_15341.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___105_15341.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___105_15341.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___105_15341.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___105_15341.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___105_15341.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___105_15341.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___105_15341.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___105_15341.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___105_15341.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___105_15341.FStar_TypeChecker_Env.dep_graph)
                        }) e11
                      in
                   match uu____15332 with
                   | (e12,c1,g1) ->
                       let uu____15355 =
                         let uu____15360 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____15365  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____15360 e12 c1 wf_annot
                          in
                       (match uu____15355 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f  in
                            ((let uu____15380 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____15380
                              then
                                let uu____15381 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____15382 =
                                  FStar_Syntax_Print.lcomp_to_string c11  in
                                let uu____15383 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____15381 uu____15382 uu____15383
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
            let uu____15417 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____15417 with
             | (univ_opening,univ_vars1) ->
                 let uu____15450 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                   univ_opening, uu____15450))
        | uu____15457 ->
            let uu____15458 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____15458 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____15507 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____15507)
                 else
                   (let uu____15515 = FStar_Syntax_Util.type_u ()  in
                    match uu____15515 with
                    | (k,uu____15535) ->
                        let uu____15536 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____15536 with
                         | (t2,uu____15558,g) ->
                             ((let uu____15561 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____15561
                               then
                                 let uu____15562 =
                                   let uu____15563 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____15563
                                    in
                                 let uu____15564 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____15562 uu____15564
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____15567 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____15567))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun uu____15575  ->
      match uu____15575 with
      | (x,imp) ->
          let uu____15594 = FStar_Syntax_Util.type_u ()  in
          (match uu____15594 with
           | (tu,u) ->
               ((let uu____15614 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____15614
                 then
                   let uu____15615 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____15616 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____15617 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____15615 uu____15616 uu____15617
                 else ());
                (let uu____15619 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____15619 with
                 | (t,uu____15639,g) ->
                     let x1 =
                       ((let uu___106_15647 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___106_15647.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___106_15647.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____15649 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       if uu____15649
                       then
                         let uu____15650 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1)
                            in
                         let uu____15651 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____15650 uu____15651
                       else ());
                      (let uu____15653 = push_binding env x1  in
                       (x1, uu____15653, g, u))))))

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
            let uu____15747 = tc_binder env1 b  in
            (match uu____15747 with
             | (b1,env',g,u) ->
                 let uu____15788 = aux env' bs2  in
                 (match uu____15788 with
                  | (bs3,env'1,g',us) ->
                      let uu____15841 =
                        let uu____15842 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g'
                           in
                        FStar_TypeChecker_Rel.conj_guard g uu____15842  in
                      ((b1 :: bs3), env'1, uu____15841, (u :: us))))
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
          (fun uu____15931  ->
             fun uu____15932  ->
               match (uu____15931, uu____15932) with
               | ((t,imp),(args1,g)) ->
                   let uu____16001 = tc_term env1 t  in
                   (match uu____16001 with
                    | (t1,uu____16019,g') ->
                        let uu____16021 =
                          FStar_TypeChecker_Rel.conj_guard g g'  in
                        (((t1, imp) :: args1), uu____16021))) args
          ([], FStar_TypeChecker_Rel.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____16063  ->
             match uu____16063 with
             | (pats1,g) ->
                 let uu____16088 = tc_args env p  in
                 (match uu____16088 with
                  | (args,g') ->
                      let uu____16101 = FStar_TypeChecker_Rel.conj_guard g g'
                         in
                      ((args :: pats1), uu____16101))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let uu____16114 = tc_maybe_toplevel_term env e  in
      match uu____16114 with
      | (e1,c,g) ->
          let uu____16130 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____16130
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c  in
             let c2 = norm_c env c1  in
             let uu____16141 =
               let uu____16146 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____16146
               then
                 let uu____16151 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____16151, false)
               else
                 (let uu____16153 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____16153, true))
                in
             match uu____16141 with
             | (target_comp,allow_ghost) ->
                 let uu____16162 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____16162 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____16172 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp  in
                      let uu____16173 =
                        FStar_TypeChecker_Rel.conj_guard g1 g'  in
                      (e1, uu____16172, uu____16173)
                  | uu____16174 ->
                      if allow_ghost
                      then
                        let uu____16183 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2
                           in
                        FStar_Errors.raise_error uu____16183
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____16195 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2
                            in
                         FStar_Errors.raise_error uu____16195
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
      let uu____16218 = tc_tot_or_gtot_term env t  in
      match uu____16218 with
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
      (let uu____16250 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____16250
       then
         let uu____16251 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____16251
       else ());
      (let env1 =
         let uu___107_16254 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___107_16254.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___107_16254.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___107_16254.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___107_16254.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___107_16254.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___107_16254.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___107_16254.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___107_16254.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___107_16254.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___107_16254.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___107_16254.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___107_16254.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___107_16254.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___107_16254.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___107_16254.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___107_16254.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___107_16254.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___107_16254.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___107_16254.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___107_16254.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___107_16254.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___107_16254.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___107_16254.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___107_16254.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___107_16254.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___107_16254.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___107_16254.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___107_16254.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___107_16254.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___107_16254.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___107_16254.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___107_16254.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___107_16254.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___107_16254.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___107_16254.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____16261 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (e1,msg,uu____16296) ->
             let uu____16297 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____16297
          in
       match uu____16261 with
       | (t,c,g) ->
           let uu____16313 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____16313
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____16323 =
                let uu____16328 =
                  let uu____16329 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____16329
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____16328)
                 in
              let uu____16330 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____16323 uu____16330))
  
let level_of_type_fail :
  'Auu____16345 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____16345
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____16361 =
          let uu____16366 =
            let uu____16367 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____16367 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____16366)  in
        let uu____16368 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____16361 uu____16368
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____16395 =
            let uu____16396 = FStar_Syntax_Util.unrefine t1  in
            uu____16396.FStar_Syntax_Syntax.n  in
          match uu____16395 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____16400 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____16403 = FStar_Syntax_Util.type_u ()  in
                 match uu____16403 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___110_16411 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___110_16411.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___110_16411.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___110_16411.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___110_16411.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___110_16411.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___110_16411.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___110_16411.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___110_16411.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___110_16411.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___110_16411.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___110_16411.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___110_16411.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___110_16411.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___110_16411.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___110_16411.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___110_16411.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___110_16411.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___110_16411.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___110_16411.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___110_16411.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___110_16411.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___110_16411.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___110_16411.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___110_16411.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___110_16411.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___110_16411.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___110_16411.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___110_16411.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___110_16411.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___110_16411.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___110_16411.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___110_16411.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___110_16411.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___110_16411.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___110_16411.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___110_16411.FStar_TypeChecker_Env.dep_graph)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____16415 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____16415
                       | uu____16416 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u))
           in
        aux true t
  
let rec (universe_of_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun e  ->
      let uu____16429 =
        let uu____16430 = FStar_Syntax_Subst.compress e  in
        uu____16430.FStar_Syntax_Syntax.n  in
      match uu____16429 with
      | FStar_Syntax_Syntax.Tm_bvar uu____16435 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____16440 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____16467 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____16483) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____16506,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____16533) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____16540 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____16540 with | ((uu____16551,t),uu____16553) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____16559 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____16559
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16560,(FStar_Util.Inl t,uu____16562),uu____16563) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16610,(FStar_Util.Inr c,uu____16612),uu____16613) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____16661 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____16670;
             FStar_Syntax_Syntax.vars = uu____16671;_},us)
          ->
          let uu____16677 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____16677 with
           | ((us',t),uu____16690) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____16696 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____16696)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____16712 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____16713 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____16723) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____16746 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____16746 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____16766  ->
                      match uu____16766 with
                      | (b,uu____16772) ->
                          let uu____16773 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____16773) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____16778 = universe_of_aux env res  in
                 level_of_type env res uu____16778  in
               let u_c =
                 let uu____16780 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res  in
                 match uu____16780 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____16784 = universe_of_aux env trepr  in
                     level_of_type env trepr uu____16784
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
            | FStar_Syntax_Syntax.Tm_bvar uu____16883 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____16898 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____16937 ->
                let uu____16938 = universe_of_aux env hd3  in
                (uu____16938, args1)
            | FStar_Syntax_Syntax.Tm_name uu____16951 ->
                let uu____16952 = universe_of_aux env hd3  in
                (uu____16952, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____16965 ->
                let uu____16982 = universe_of_aux env hd3  in
                (uu____16982, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____16995 ->
                let uu____17002 = universe_of_aux env hd3  in
                (uu____17002, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____17015 ->
                let uu____17042 = universe_of_aux env hd3  in
                (uu____17042, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____17055 ->
                let uu____17062 = universe_of_aux env hd3  in
                (uu____17062, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____17075 ->
                let uu____17076 = universe_of_aux env hd3  in
                (uu____17076, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____17089 ->
                let uu____17102 = universe_of_aux env hd3  in
                (uu____17102, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____17115 ->
                let uu____17122 = universe_of_aux env hd3  in
                (uu____17122, args1)
            | FStar_Syntax_Syntax.Tm_type uu____17135 ->
                let uu____17136 = universe_of_aux env hd3  in
                (uu____17136, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____17149,hd4::uu____17151) ->
                let uu____17216 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____17216 with
                 | (uu____17231,uu____17232,hd5) ->
                     let uu____17250 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____17250 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____17301 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env e
                   in
                let uu____17303 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____17303 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____17354 ->
                let uu____17355 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____17355 with
                 | (env1,uu____17377) ->
                     let env2 =
                       let uu___111_17383 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___111_17383.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___111_17383.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___111_17383.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___111_17383.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___111_17383.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___111_17383.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___111_17383.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___111_17383.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___111_17383.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___111_17383.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___111_17383.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___111_17383.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___111_17383.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___111_17383.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___111_17383.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___111_17383.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___111_17383.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___111_17383.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___111_17383.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___111_17383.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___111_17383.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___111_17383.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___111_17383.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___111_17383.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___111_17383.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___111_17383.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___111_17383.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___111_17383.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___111_17383.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___111_17383.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___111_17383.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___111_17383.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___111_17383.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___111_17383.FStar_TypeChecker_Env.dep_graph)
                       }  in
                     ((let uu____17385 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____17385
                       then
                         let uu____17386 =
                           let uu____17387 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____17387  in
                         let uu____17388 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____17386 uu____17388
                       else ());
                      (let uu____17390 = tc_term env2 hd3  in
                       match uu____17390 with
                       | (uu____17411,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____17412;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____17414;
                                        FStar_Syntax_Syntax.comp_thunk =
                                          uu____17415;_},g)
                           ->
                           ((let uu____17435 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____17435
                               (fun a239  -> ()));
                            (t, args1)))))
             in
          let uu____17446 = type_of_head true hd1 args  in
          (match uu____17446 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t
                  in
               let uu____17486 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____17486 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____17530 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____17530)))
      | FStar_Syntax_Syntax.Tm_match (uu____17533,hd1::uu____17535) ->
          let uu____17600 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____17600 with
           | (uu____17603,uu____17604,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____17622,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____17669 = universe_of_aux env e  in
      level_of_type env e uu____17669
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tps  ->
      let uu____17692 = tc_binders env tps  in
      match uu____17692 with
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
      let uu____17746 =
        let uu____17747 = FStar_Syntax_Subst.compress t  in
        uu____17747.FStar_Syntax_Syntax.n  in
      match uu____17746 with
      | FStar_Syntax_Syntax.Tm_delayed uu____17752 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____17779 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____17786 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____17786
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____17788 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____17788
            (fun uu____17802  ->
               match uu____17802 with
               | (t1,uu____17810) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____17812;
             FStar_Syntax_Syntax.vars = uu____17813;_},us)
          ->
          let uu____17819 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____17819
            (fun uu____17833  ->
               match uu____17833 with
               | (t1,uu____17841) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____17843 = tc_constant env t.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____17843
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____17845 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____17845
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____17854;_})
          ->
          let mk_comp =
            let uu____17890 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____17890
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____17910 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____17910
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____17957 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____17957
                 (fun u  ->
                    let uu____17965 =
                      let uu____17968 =
                        let uu____17975 =
                          let uu____17976 =
                            let uu____17989 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____17989)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____17976  in
                        FStar_Syntax_Syntax.mk uu____17975  in
                      uu____17968 FStar_Pervasives_Native.None
                        t.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____17965))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____18019 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____18019 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____18072 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____18072
                       (fun uc  ->
                          let uu____18080 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____18080)
                 | (x,imp)::bs3 ->
                     let uu____18098 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____18098
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____18107 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____18125) ->
          let uu____18130 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____18130
            (fun u_x  ->
               let uu____18138 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____18138)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____18176 =
              let uu____18177 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____18177.FStar_Syntax_Syntax.n  in
            match uu____18176 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____18239 = FStar_Util.first_N n_args bs  in
                    match uu____18239 with
                    | (bs1,rest) ->
                        let t1 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____18309 =
                          let uu____18314 = FStar_Syntax_Syntax.mk_Total t1
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____18314  in
                        (match uu____18309 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____18350 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____18350 with
                       | (bs1,c1) ->
                           let uu____18365 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____18365
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____18407  ->
                     match uu____18407 with
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
                         let uu____18453 = FStar_Syntax_Subst.subst subst1 t1
                            in
                         FStar_Pervasives_Native.Some uu____18453)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____18455) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____18461,uu____18462) ->
                aux t1
            | uu____18503 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____18504,(FStar_Util.Inl t1,uu____18506),uu____18507) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____18556,(FStar_Util.Inr c,uu____18558),uu____18559) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (uu____18608,t1) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____18643) ->
          type_of_well_typed_term env t1
      | FStar_Syntax_Syntax.Tm_match uu____18648 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____18671 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____18684 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____18695 = type_of_well_typed_term env t  in
      match uu____18695 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____18701;
            FStar_Syntax_Syntax.vars = uu____18702;_}
          -> FStar_Pervasives_Native.Some u
      | uu____18707 -> FStar_Pervasives_Native.None

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
            let uu___112_18732 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___112_18732.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___112_18732.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___112_18732.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___112_18732.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___112_18732.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___112_18732.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___112_18732.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___112_18732.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___112_18732.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___112_18732.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___112_18732.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___112_18732.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___112_18732.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___112_18732.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___112_18732.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___112_18732.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___112_18732.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___112_18732.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___112_18732.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___112_18732.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___112_18732.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___112_18732.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___112_18732.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___112_18732.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___112_18732.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___112_18732.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___112_18732.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___112_18732.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___112_18732.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___112_18732.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___112_18732.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___112_18732.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___112_18732.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___112_18732.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___112_18732.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___112_18732.FStar_TypeChecker_Env.dep_graph)
            }  in
          let slow_check uu____18738 =
            if must_total
            then
              let uu____18739 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____18739 with | (uu____18746,uu____18747,g) -> g
            else
              (let uu____18750 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____18750 with | (uu____18757,uu____18758,g) -> g)
             in
          let uu____18760 =
            let uu____18761 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____18761  in
          if uu____18760
          then slow_check ()
          else
            (let uu____18763 = type_of_well_typed_term env2 t  in
             match uu____18763 with
             | FStar_Pervasives_Native.None  -> slow_check ()
             | FStar_Pervasives_Native.Some k' ->
                 ((let uu____18768 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                       (FStar_Options.Other "FastImplicits")
                      in
                   if uu____18768
                   then
                     let uu____18769 =
                       FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                        in
                     let uu____18770 = FStar_Syntax_Print.term_to_string t
                        in
                     let uu____18771 = FStar_Syntax_Print.term_to_string k'
                        in
                     let uu____18772 = FStar_Syntax_Print.term_to_string k
                        in
                     FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                       uu____18769 uu____18770 uu____18771 uu____18772
                   else ());
                  (let b = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                   (let uu____18776 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                        (FStar_Options.Other "FastImplicits")
                       in
                    if uu____18776
                    then
                      let uu____18777 =
                        FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                         in
                      let uu____18778 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____18779 = FStar_Syntax_Print.term_to_string k'
                         in
                      let uu____18780 = FStar_Syntax_Print.term_to_string k
                         in
                      FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                        uu____18777 (if b then "succeeded" else "failed")
                        uu____18778 uu____18779 uu____18780
                    else ());
                   if b
                   then FStar_TypeChecker_Rel.trivial_guard
                   else slow_check ())))
  