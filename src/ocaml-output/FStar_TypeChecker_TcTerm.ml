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
        (let uu___72_2024 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___72_2024.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___72_2024.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___72_2024.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___72_2024.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___72_2024.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___72_2024.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___72_2024.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___72_2024.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___72_2024.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___72_2024.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___72_2024.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___72_2024.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___72_2024.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___72_2024.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___72_2024.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___72_2024.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___72_2024.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___72_2024.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___72_2024.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___72_2024.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___72_2024.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___72_2024.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___72_2024.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___72_2024.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___72_2024.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___72_2024.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___72_2024.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___72_2024.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___72_2024.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___72_2024.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___72_2024.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___72_2024.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___72_2024.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___72_2024.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___72_2024.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___72_2024.FStar_TypeChecker_Env.dep_graph)
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
      (let uu____2036 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____2036
       then
         let uu____2037 =
           let uu____2038 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____2038  in
         let uu____2039 = FStar_Syntax_Print.tag_of_term e  in
         FStar_Util.print2 "%s (%s)\n" uu____2037 uu____2039
       else ());
      (let top = FStar_Syntax_Subst.compress e  in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2048 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____2079 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____2086 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____2103 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____2104 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____2105 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____2106 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____2107 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____2124 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____2137 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____2144 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted
           (uu____2145,{
                         FStar_Syntax_Syntax.qkind =
                           FStar_Syntax_Syntax.Quote_static ;
                         FStar_Syntax_Syntax.antiquotes = aqs;_})
           when
           FStar_List.for_all
             (fun uu____2173  ->
                match uu____2173 with
                | (uu____2182,b,uu____2184) -> Prims.op_Negation b) aqs
           ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl FStar_Syntax_Syntax.t_term)
             FStar_TypeChecker_Rel.trivial_guard
       | FStar_Syntax_Syntax.Tm_quoted uu____2189 ->
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
           let uu____2203 =
             let uu____2210 =
               let uu____2215 = FStar_Syntax_Util.lcomp_of_comp c  in
               FStar_Util.Inr uu____2215  in
             value_check_expected_typ env1 top uu____2210
               FStar_TypeChecker_Rel.trivial_guard
              in
           (match uu____2203 with
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
           let uu____2238 = tc_tot_or_gtot_term env1 e1  in
           (match uu____2238 with
            | (e2,c,g) ->
                let g1 =
                  let uu___73_2255 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___73_2255.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___73_2255.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___73_2255.FStar_TypeChecker_Env.implicits)
                  }  in
                let uu____2256 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____2256, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____2277 = FStar_Syntax_Util.type_u ()  in
           (match uu____2277 with
            | (t,u) ->
                let uu____2290 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____2290 with
                 | (e2,c,g) ->
                     let uu____2306 =
                       let uu____2321 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____2321 with
                       | (env2,uu____2343) -> tc_pats env2 pats  in
                     (match uu____2306 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___74_2377 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___74_2377.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___74_2377.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___74_2377.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____2378 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____2381 =
                            FStar_TypeChecker_Rel.conj_guard g g'1  in
                          (uu____2378, c, uu____2381))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____2389 =
             let uu____2390 = FStar_Syntax_Subst.compress e1  in
             uu____2390.FStar_Syntax_Syntax.n  in
           (match uu____2389 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____2399,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____2401;
                               FStar_Syntax_Syntax.lbtyp = uu____2402;
                               FStar_Syntax_Syntax.lbeff = uu____2403;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____2405;
                               FStar_Syntax_Syntax.lbpos = uu____2406;_}::[]),e2)
                ->
                let uu____2434 =
                  let uu____2441 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____2441 e11  in
                (match uu____2434 with
                 | (e12,c1,g1) ->
                     let uu____2451 = tc_term env1 e2  in
                     (match uu____2451 with
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
                            let uu____2475 =
                              let uu____2482 =
                                let uu____2483 =
                                  let uu____2496 =
                                    let uu____2503 =
                                      let uu____2506 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____2506]  in
                                    (false, uu____2503)  in
                                  (uu____2496, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____2483  in
                              FStar_Syntax_Syntax.mk uu____2482  in
                            uu____2475 FStar_Pervasives_Native.None
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
                          let uu____2528 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2  in
                          (e5, c, uu____2528)))
            | uu____2531 ->
                let uu____2532 = tc_term env1 e1  in
                (match uu____2532 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2554) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____2566) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____2585 = tc_term env1 e1  in
           (match uu____2585 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____2609) ->
           let uu____2656 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____2656 with
            | (env0,uu____2670) ->
                let uu____2675 = tc_comp env0 expected_c  in
                (match uu____2675 with
                 | (expected_c1,uu____2689,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1
                        in
                     let uu____2694 =
                       let uu____2701 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res
                          in
                       tc_term uu____2701 e1  in
                     (match uu____2694 with
                      | (e2,c',g') ->
                          let uu____2711 =
                            let uu____2718 =
                              let uu____2723 =
                                FStar_Syntax_Syntax.lcomp_comp c'  in
                              (e2, uu____2723)  in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____2718
                             in
                          (match uu____2711 with
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
                                 let uu____2771 =
                                   FStar_TypeChecker_Rel.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____2771
                                  in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____2783 =
                                            FStar_Syntax_Util.mk_squash
                                              FStar_Syntax_Syntax.U_zero f1
                                             in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____2783)
                                  in
                               let uu____2784 =
                                 comp_check_expected_typ env1 e4 lc  in
                               (match uu____2784 with
                                | (e5,c,f2) ->
                                    let final_guard =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2
                                       in
                                    (e5, c, final_guard))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____2804) ->
           let uu____2851 = FStar_Syntax_Util.type_u ()  in
           (match uu____2851 with
            | (k,u) ->
                let uu____2864 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____2864 with
                 | (t1,uu____2878,f) ->
                     let uu____2880 =
                       let uu____2887 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                       tc_term uu____2887 e1  in
                     (match uu____2880 with
                      | (e2,c,g) ->
                          let uu____2897 =
                            let uu____2902 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____2907  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____2902 e2 c f
                             in
                          (match uu____2897 with
                           | (c1,f1) ->
                               let uu____2916 =
                                 let uu____2923 =
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
                                 comp_check_expected_typ env1 uu____2923 c1
                                  in
                               (match uu____2916 with
                                | (e3,c2,f2) ->
                                    let uu____2963 =
                                      let uu____2964 =
                                        FStar_TypeChecker_Rel.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____2964
                                       in
                                    (e3, c2, uu____2963))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____2965;
              FStar_Syntax_Syntax.vars = uu____2966;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3029 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3029 with
            | (unary_op,uu____3051) ->
                let head1 =
                  let uu____3075 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3075
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
              FStar_Syntax_Syntax.pos = uu____3113;
              FStar_Syntax_Syntax.vars = uu____3114;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3177 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3177 with
            | (unary_op,uu____3199) ->
                let head1 =
                  let uu____3223 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3223
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
                (FStar_Const.Const_reflect uu____3261);
              FStar_Syntax_Syntax.pos = uu____3262;
              FStar_Syntax_Syntax.vars = uu____3263;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3326 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3326 with
            | (unary_op,uu____3348) ->
                let head1 =
                  let uu____3372 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3372
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
              FStar_Syntax_Syntax.pos = uu____3410;
              FStar_Syntax_Syntax.vars = uu____3411;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3487 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3487 with
            | (unary_op,uu____3509) ->
                let head1 =
                  let uu____3533 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____3533
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
              FStar_Syntax_Syntax.pos = uu____3577;
              FStar_Syntax_Syntax.vars = uu____3578;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____3616 =
             let uu____3623 =
               let uu____3624 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3624  in
             tc_term uu____3623 e1  in
           (match uu____3616 with
            | (e2,c,g) ->
                let uu____3648 = FStar_Syntax_Util.head_and_args top  in
                (match uu____3648 with
                 | (head1,uu____3670) ->
                     let uu____3691 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____3718 =
                       let uu____3719 =
                         let uu____3722 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____3722  in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____3719
                        in
                     (uu____3691, uu____3718, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3727;
              FStar_Syntax_Syntax.vars = uu____3728;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____3781 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3781 with
            | (head1,uu____3803) ->
                let env' =
                  let uu____3825 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____3825  in
                let uu____3826 = tc_term env' r  in
                (match uu____3826 with
                 | (er,uu____3840,gr) ->
                     let uu____3842 = tc_term env1 t  in
                     (match uu____3842 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Rel.conj_guard gr gt1  in
                          let uu____3859 =
                            let uu____3862 =
                              let uu____3867 =
                                let uu____3868 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____3869 =
                                  let uu____3872 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____3872]  in
                                uu____3868 :: uu____3869  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____3867
                               in
                            uu____3862 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____3859, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3877;
              FStar_Syntax_Syntax.vars = uu____3878;_},uu____3879)
           ->
           let uu____3900 =
             let uu____3905 =
               let uu____3906 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____3906  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____3905)  in
           FStar_Errors.raise_error uu____3900 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3913;
              FStar_Syntax_Syntax.vars = uu____3914;_},uu____3915)
           ->
           let uu____3936 =
             let uu____3941 =
               let uu____3942 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____3942  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____3941)  in
           FStar_Errors.raise_error uu____3936 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____3949;
              FStar_Syntax_Syntax.vars = uu____3950;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____3983 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____3983 with
             | (env0,uu____3997) ->
                 let uu____4002 = tc_term env0 e1  in
                 (match uu____4002 with
                  | (e2,c,g) ->
                      let uu____4018 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____4018 with
                       | (reify_op,uu____4040) ->
                           let u_c =
                             let uu____4062 =
                               tc_term env0 c.FStar_Syntax_Syntax.res_typ  in
                             match uu____4062 with
                             | (uu____4069,c',uu____4071) ->
                                 let uu____4072 =
                                   let uu____4073 =
                                     FStar_Syntax_Subst.compress
                                       c'.FStar_Syntax_Syntax.res_typ
                                      in
                                   uu____4073.FStar_Syntax_Syntax.n  in
                                 (match uu____4072 with
                                  | FStar_Syntax_Syntax.Tm_type u -> u
                                  | uu____4077 ->
                                      let uu____4078 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____4078 with
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
                                                 let uu____4090 =
                                                   let uu____4091 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       c'
                                                      in
                                                   let uu____4092 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   let uu____4093 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c'.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   FStar_Util.format3
                                                     "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                     uu____4091 uu____4092
                                                     uu____4093
                                                    in
                                                 failwith uu____4090);
                                            u)))
                              in
                           let repr =
                             let uu____4095 =
                               FStar_Syntax_Syntax.lcomp_comp c  in
                             FStar_TypeChecker_Env.reify_comp env1 uu____4095
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
                             let uu____4116 =
                               FStar_Syntax_Syntax.mk_Total repr  in
                             FStar_All.pipe_right uu____4116
                               FStar_Syntax_Util.lcomp_of_comp
                              in
                           let uu____4117 =
                             comp_check_expected_typ env1 e3 c1  in
                           (match uu____4117 with
                            | (e4,c2,g') ->
                                let uu____4133 =
                                  FStar_TypeChecker_Rel.conj_guard g g'  in
                                (e4, c2, uu____4133))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____4135;
              FStar_Syntax_Syntax.vars = uu____4136;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let no_reflect uu____4180 =
               let uu____4181 =
                 let uu____4186 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____4186)  in
               FStar_Errors.raise_error uu____4181 e1.FStar_Syntax_Syntax.pos
                in
             let uu____4193 = FStar_Syntax_Util.head_and_args top  in
             match uu____4193 with
             | (reflect_op,uu____4215) ->
                 let uu____4236 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____4236 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____4269 =
                        let uu____4270 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable
                           in
                        Prims.op_Negation uu____4270  in
                      if uu____4269
                      then no_reflect ()
                      else
                        (let uu____4280 =
                           FStar_TypeChecker_Env.clear_expected_typ env1  in
                         match uu____4280 with
                         | (env_no_ex,topt) ->
                             let uu____4299 =
                               let u = FStar_TypeChecker_Env.new_u_univ ()
                                  in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr))
                                  in
                               let t =
                                 let uu____4319 =
                                   let uu____4326 =
                                     let uu____4327 =
                                       let uu____4342 =
                                         let uu____4345 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         let uu____4346 =
                                           let uu____4349 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun
                                              in
                                           [uu____4349]  in
                                         uu____4345 :: uu____4346  in
                                       (repr, uu____4342)  in
                                     FStar_Syntax_Syntax.Tm_app uu____4327
                                      in
                                   FStar_Syntax_Syntax.mk uu____4326  in
                                 uu____4319 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let uu____4355 =
                                 let uu____4362 =
                                   let uu____4363 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1
                                      in
                                   FStar_All.pipe_right uu____4363
                                     FStar_Pervasives_Native.fst
                                    in
                                 tc_tot_or_gtot_term uu____4362 t  in
                               match uu____4355 with
                               | (t1,uu____4391,g) ->
                                   let uu____4393 =
                                     let uu____4394 =
                                       FStar_Syntax_Subst.compress t1  in
                                     uu____4394.FStar_Syntax_Syntax.n  in
                                   (match uu____4393 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____4409,(res,uu____4411)::
                                         (wp,uu____4413)::[])
                                        -> (t1, res, wp, g)
                                    | uu____4456 -> failwith "Impossible")
                                in
                             (match uu____4299 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____4487 =
                                    let uu____4492 =
                                      tc_tot_or_gtot_term env_no_ex e1  in
                                    match uu____4492 with
                                    | (e2,c,g) ->
                                        ((let uu____4507 =
                                            let uu____4508 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c
                                               in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____4508
                                             in
                                          if uu____4507
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [(FStar_Errors.Error_UnexpectedGTotComputation,
                                                 "Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____4522 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ
                                             in
                                          match uu____4522 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____4530 =
                                                  let uu____4539 =
                                                    let uu____4546 =
                                                      let uu____4547 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr
                                                         in
                                                      let uu____4548 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____4547 uu____4548
                                                       in
                                                    (FStar_Errors.Error_UnexpectedInstance,
                                                      uu____4546,
                                                      (e2.FStar_Syntax_Syntax.pos))
                                                     in
                                                  [uu____4539]  in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____4530);
                                               (let uu____4561 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                (e2, uu____4561)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____4563 =
                                                let uu____4564 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____4564
                                                 in
                                              (e2, uu____4563)))
                                     in
                                  (match uu____4487 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____4574 =
                                           let uu____4575 =
                                             let uu____4576 =
                                               let uu____4577 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ
                                                  in
                                               [uu____4577]  in
                                             let uu____4578 =
                                               let uu____4587 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp
                                                  in
                                               [uu____4587]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____4576;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____4578;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____4575
                                            in
                                         FStar_All.pipe_right uu____4574
                                           FStar_Syntax_Util.lcomp_of_comp
                                          in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____4607 =
                                         comp_check_expected_typ env1 e3 c
                                          in
                                       (match uu____4607 with
                                        | (e4,c1,g') ->
                                            let uu____4623 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g
                                               in
                                            (e4, c1, uu____4623))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____4670 =
               let uu____4671 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____4671 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____4670 instantiate_both  in
           ((let uu____4687 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____4687
             then
               let uu____4688 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____4689 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____4688
                 uu____4689
             else ());
            (let uu____4691 = tc_term (no_inst env2) head1  in
             match uu____4691 with
             | (head2,chead,g_head) ->
                 let uu____4707 =
                   let uu____4714 =
                     ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                        (let uu____4716 = FStar_Options.lax ()  in
                         Prims.op_Negation uu____4716))
                       && (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____4714
                   then
                     let uu____4723 =
                       let uu____4730 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____4730
                        in
                     match uu____4723 with | (e1,c,g) -> (e1, c, g)
                   else
                     (let uu____4743 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env2 head2 chead g_head args
                        uu____4743)
                    in
                 (match uu____4707 with
                  | (e1,c,g) ->
                      ((let uu____4756 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme
                           in
                        if uu____4756
                        then
                          let uu____4757 =
                            FStar_TypeChecker_Rel.print_pending_implicits g
                             in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____4757
                        else ());
                       (let uu____4759 = comp_check_expected_typ env0 e1 c
                           in
                        match uu____4759 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____4776 =
                                let uu____4777 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____4777.FStar_Syntax_Syntax.n  in
                              match uu____4776 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____4781) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos))
                                     in
                                  let uu___75_4843 =
                                    FStar_TypeChecker_Rel.trivial_guard  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___75_4843.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___75_4843.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___75_4843.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____4892 ->
                                  FStar_TypeChecker_Rel.trivial_guard
                               in
                            let gres =
                              let uu____4894 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp  in
                              FStar_TypeChecker_Rel.conj_guard g uu____4894
                               in
                            ((let uu____4896 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme
                                 in
                              if uu____4896
                              then
                                let uu____4897 =
                                  FStar_Syntax_Print.term_to_string e2  in
                                let uu____4898 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres
                                   in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____4897 uu____4898
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____4938 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____4938 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____4958 = tc_term env12 e1  in
                (match uu____4958 with
                 | (e11,c1,g1) ->
                     let uu____4974 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____4984 = FStar_Syntax_Util.type_u ()  in
                           (match uu____4984 with
                            | (k,uu____4994) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k  in
                                let uu____4996 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t
                                   in
                                (uu____4996, res_t))
                        in
                     (match uu____4974 with
                      | (env_branches,res_t) ->
                          ((let uu____5006 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____5006
                            then
                              let uu____5007 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____5007
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
                            let uu____5120 =
                              let uu____5125 =
                                FStar_List.fold_right
                                  (fun uu____5200  ->
                                     fun uu____5201  ->
                                       match (uu____5200, uu____5201) with
                                       | ((branch1,f,eff_label,cflags,c,g),
                                          (caccum,gaccum)) ->
                                           let uu____5415 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum
                                              in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____5415)) t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard)
                                 in
                              match uu____5125 with
                              | (cases,g) ->
                                  let uu____5513 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____5513, g)
                               in
                            match uu____5120 with
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
                                           (fun uu____5631  ->
                                              match uu____5631 with
                                              | ((pat,wopt,br),uu____5667,eff_label,uu____5669,uu____5670,uu____5671)
                                                  ->
                                                  let uu____5694 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t
                                                     in
                                                  (pat, wopt, uu____5694)))
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
                                  let uu____5749 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____5749
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____5756 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____5756  in
                                     let lb =
                                       let uu____5760 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name
                                          in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_Syntax_Syntax.res_typ
                                         uu____5760 e11 []
                                         e11.FStar_Syntax_Syntax.pos
                                        in
                                     let e2 =
                                       let uu____5766 =
                                         let uu____5773 =
                                           let uu____5774 =
                                             let uu____5787 =
                                               let uu____5788 =
                                                 let uu____5789 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____5789]  in
                                               FStar_Syntax_Subst.close
                                                 uu____5788 e_match
                                                in
                                             ((false, [lb]), uu____5787)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____5774
                                            in
                                         FStar_Syntax_Syntax.mk uu____5773
                                          in
                                       uu____5766
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____5802 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____5802
                                  then
                                    let uu____5803 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____5804 =
                                      FStar_Syntax_Print.lcomp_to_string cres
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____5803 uu____5804
                                  else ());
                                 (let uu____5806 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches
                                     in
                                  (e2, cres, uu____5806))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5809;
                FStar_Syntax_Syntax.lbunivs = uu____5810;
                FStar_Syntax_Syntax.lbtyp = uu____5811;
                FStar_Syntax_Syntax.lbeff = uu____5812;
                FStar_Syntax_Syntax.lbdef = uu____5813;
                FStar_Syntax_Syntax.lbattrs = uu____5814;
                FStar_Syntax_Syntax.lbpos = uu____5815;_}::[]),uu____5816)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____5839),uu____5840) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5855;
                FStar_Syntax_Syntax.lbunivs = uu____5856;
                FStar_Syntax_Syntax.lbtyp = uu____5857;
                FStar_Syntax_Syntax.lbeff = uu____5858;
                FStar_Syntax_Syntax.lbdef = uu____5859;
                FStar_Syntax_Syntax.lbattrs = uu____5860;
                FStar_Syntax_Syntax.lbpos = uu____5861;_}::uu____5862),uu____5863)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____5888),uu____5889) ->
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
        let uu____5915 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____6005))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____6064 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_SynthByTacticError,
                  "synth_by_tactic: bad application") rng
           in
        match uu____5915 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____6148 = FStar_TypeChecker_Env.expected_typ env  in
                  (match uu____6148 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____6154 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_SynthByTacticError,
                           "synth_by_tactic: need a type annotation when no expected type is present")
                         uu____6154)
               in
            let uu____6157 = FStar_TypeChecker_Env.clear_expected_typ env  in
            (match uu____6157 with
             | (env',uu____6171) ->
                 let uu____6176 = tc_term env' typ  in
                 (match uu____6176 with
                  | (typ1,uu____6190,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____6193 = tc_tactic env' tau  in
                        match uu____6193 with
                        | (tau1,uu____6207,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let t =
                                if env.FStar_TypeChecker_Env.nosynth
                                then
                                  let uu____6215 =
                                    let uu____6220 =
                                      FStar_TypeChecker_Util.fvar_const env
                                        FStar_Parser_Const.magic_lid
                                       in
                                    let uu____6221 =
                                      let uu____6222 =
                                        FStar_Syntax_Syntax.as_arg
                                          FStar_Syntax_Util.exp_unit
                                         in
                                      [uu____6222]  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6220
                                      uu____6221
                                     in
                                  uu____6215 FStar_Pervasives_Native.None rng
                                else
                                  (let t =
                                     env.FStar_TypeChecker_Env.synth_hook
                                       env' typ1 tau1
                                      in
                                   (let uu____6228 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Tac")
                                       in
                                    if uu____6228
                                    then
                                      let uu____6229 =
                                        FStar_Syntax_Print.term_to_string t
                                         in
                                      FStar_Util.print1 "Got %s\n" uu____6229
                                    else ());
                                   t)
                                 in
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____6232 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng
                                  in
                               tc_term env uu____6232)))))))

and (tc_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___76_6236 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___76_6236.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___76_6236.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___76_6236.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___76_6236.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___76_6236.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___76_6236.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___76_6236.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___76_6236.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___76_6236.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___76_6236.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___76_6236.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___76_6236.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___76_6236.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___76_6236.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___76_6236.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___76_6236.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___76_6236.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___76_6236.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___76_6236.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___76_6236.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___76_6236.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___76_6236.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___76_6236.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___76_6236.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___76_6236.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___76_6236.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___76_6236.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___76_6236.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___76_6236.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___76_6236.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___76_6236.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___76_6236.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___76_6236.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___76_6236.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___76_6236.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___76_6236.FStar_TypeChecker_Env.dep_graph)
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
        let uu___77_6240 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___77_6240.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___77_6240.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___77_6240.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___77_6240.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___77_6240.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___77_6240.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___77_6240.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___77_6240.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___77_6240.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___77_6240.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___77_6240.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___77_6240.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___77_6240.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___77_6240.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___77_6240.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___77_6240.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___77_6240.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___77_6240.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___77_6240.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___77_6240.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___77_6240.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___77_6240.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___77_6240.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___77_6240.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___77_6240.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___77_6240.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___77_6240.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___77_6240.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.proof_ns =
            (uu___77_6240.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___77_6240.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___77_6240.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___77_6240.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___77_6240.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___77_6240.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___77_6240.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___77_6240.FStar_TypeChecker_Env.dep_graph)
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
          let uu____6260 = tc_tactic env tactic  in
          (match uu____6260 with
           | (tactic1,uu____6272,uu____6273) ->
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
        let uu____6322 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____6322 with
        | (e2,t,implicits) ->
            let tc =
              let uu____6343 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____6343
              then FStar_Util.Inl t
              else
                (let uu____6349 =
                   let uu____6350 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____6350
                    in
                 FStar_Util.Inr uu____6349)
               in
            let is_data_ctor uu___65_6362 =
              match uu___65_6362 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____6365) -> true
              | uu____6372 -> false  in
            let uu____6375 =
              (is_data_ctor dc) &&
                (let uu____6377 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____6377)
               in
            if uu____6375
            then
              let uu____6384 =
                let uu____6389 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____6389)  in
              let uu____6390 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____6384 uu____6390
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____6407 =
            let uu____6408 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____6408
             in
          failwith uu____6407
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____6442 =
              let uu____6443 = FStar_Syntax_Subst.compress t1  in
              uu____6443.FStar_Syntax_Syntax.n  in
            match uu____6442 with
            | FStar_Syntax_Syntax.Tm_arrow uu____6446 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____6459 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos))
                   in
                let uu___78_6497 = FStar_TypeChecker_Rel.trivial_guard  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___78_6497.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___78_6497.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___78_6497.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                }
             in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____6549 =
            let uu____6562 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____6562 with
            | FStar_Pervasives_Native.None  ->
                let uu____6577 = FStar_Syntax_Util.type_u ()  in
                (match uu____6577 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard)
             in
          (match uu____6549 with
           | (t,uu____6614,g0) ->
               let uu____6628 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____6628 with
                | (e1,uu____6648,g1) ->
                    let uu____6662 =
                      let uu____6663 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____6663
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____6664 = FStar_TypeChecker_Rel.conj_guard g0 g1
                       in
                    (e1, uu____6662, uu____6664)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____6666 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____6679 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____6679)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____6666 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___79_6698 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___79_6698.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___79_6698.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____6701 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____6701 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____6722 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____6722
                       then FStar_Util.Inl t1
                       else
                         (let uu____6728 =
                            let uu____6729 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____6729
                             in
                          FStar_Util.Inr uu____6728)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6735;
             FStar_Syntax_Syntax.vars = uu____6736;_},uu____6737)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____6742 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____6742
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____6750 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____6750
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6758;
             FStar_Syntax_Syntax.vars = uu____6759;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____6768 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6768 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____6791 =
                     let uu____6796 =
                       let uu____6797 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____6798 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____6799 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____6797 uu____6798 uu____6799
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____6796)
                      in
                   let uu____6800 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____6791 uu____6800)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____6816 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6820 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6820 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6822 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6822 with
           | ((us,t),range) ->
               ((let uu____6845 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____6845
                 then
                   let uu____6846 =
                     let uu____6847 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____6847  in
                   let uu____6848 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____6849 = FStar_Range.string_of_range range  in
                   let uu____6850 = FStar_Range.string_of_use_range range  in
                   let uu____6851 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____6846 uu____6848 uu____6849 uu____6850 uu____6851
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6856 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6856 us  in
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
          let uu____6880 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6880 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____6894 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____6894 with
                | (env2,uu____6908) ->
                    let uu____6913 = tc_binders env2 bs1  in
                    (match uu____6913 with
                     | (bs2,env3,g,us) ->
                         let uu____6932 = tc_comp env3 c1  in
                         (match uu____6932 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___80_6951 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___80_6951.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___80_6951.FStar_Syntax_Syntax.vars)
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
                                  let uu____6960 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____6960
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
          let uu____6979 =
            let uu____6984 =
              let uu____6985 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____6985]  in
            FStar_Syntax_Subst.open_term uu____6984 phi  in
          (match uu____6979 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____6995 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____6995 with
                | (env2,uu____7009) ->
                    let uu____7014 =
                      let uu____7027 = FStar_List.hd x1  in
                      tc_binder env2 uu____7027  in
                    (match uu____7014 with
                     | (x2,env3,f1,u) ->
                         ((let uu____7055 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____7055
                           then
                             let uu____7056 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____7057 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____7058 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____7056 uu____7057 uu____7058
                           else ());
                          (let uu____7060 = FStar_Syntax_Util.type_u ()  in
                           match uu____7060 with
                           | (t_phi,uu____7072) ->
                               let uu____7073 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____7073 with
                                | (phi2,uu____7087,f2) ->
                                    let e1 =
                                      let uu___81_7092 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___81_7092.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___81_7092.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____7099 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____7099
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____7112) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____7135 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
            if uu____7135
            then
              let uu____7136 =
                FStar_Syntax_Print.term_to_string
                  (let uu___82_7139 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___82_7139.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___82_7139.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____7136
            else ());
           (let uu____7145 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____7145 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____7158 ->
          let uu____7159 =
            let uu____7160 = FStar_Syntax_Print.term_to_string top  in
            let uu____7161 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____7160
              uu____7161
             in
          failwith uu____7159

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____7171 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____7172,FStar_Pervasives_Native.None ) ->
            FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____7183,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____7199 -> FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_float uu____7204 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____7205 ->
            let uu____7206 =
              let uu____7211 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
                 in
              FStar_All.pipe_right uu____7211 FStar_Util.must  in
            FStar_All.pipe_right uu____7206 FStar_Pervasives_Native.fst
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____7236 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____7237 =
              let uu____7242 =
                let uu____7243 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7243
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7242)  in
            FStar_Errors.raise_error uu____7237 r
        | FStar_Const.Const_set_range_of  ->
            let uu____7244 =
              let uu____7249 =
                let uu____7250 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7250
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7249)  in
            FStar_Errors.raise_error uu____7244 r
        | FStar_Const.Const_reify  ->
            let uu____7251 =
              let uu____7256 =
                let uu____7257 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7257
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7256)  in
            FStar_Errors.raise_error uu____7251 r
        | FStar_Const.Const_reflect uu____7258 ->
            let uu____7259 =
              let uu____7264 =
                let uu____7265 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7265
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7264)  in
            FStar_Errors.raise_error uu____7259 r
        | uu____7266 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____7283) ->
          let uu____7292 = FStar_Syntax_Util.type_u ()  in
          (match uu____7292 with
           | (k,u) ->
               let uu____7305 = tc_check_tot_or_gtot_term env t k  in
               (match uu____7305 with
                | (t1,uu____7319,g) ->
                    let uu____7321 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____7321, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____7323) ->
          let uu____7332 = FStar_Syntax_Util.type_u ()  in
          (match uu____7332 with
           | (k,u) ->
               let uu____7345 = tc_check_tot_or_gtot_term env t k  in
               (match uu____7345 with
                | (t1,uu____7359,g) ->
                    let uu____7361 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____7361, u, g)))
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
            let uu____7369 =
              let uu____7374 =
                let uu____7375 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____7375 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____7374  in
            uu____7369 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____7378 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____7378 with
           | (tc1,uu____7392,f) ->
               let uu____7394 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____7394 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____7438 =
                        let uu____7439 = FStar_Syntax_Subst.compress head3
                           in
                        uu____7439.FStar_Syntax_Syntax.n  in
                      match uu____7438 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____7442,us) -> us
                      | uu____7448 -> []  in
                    let uu____7449 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____7449 with
                     | (uu____7470,args1) ->
                         let uu____7492 =
                           let uu____7511 = FStar_List.hd args1  in
                           let uu____7524 = FStar_List.tl args1  in
                           (uu____7511, uu____7524)  in
                         (match uu____7492 with
                          | (res,args2) ->
                              let uu____7589 =
                                let uu____7598 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___66_7626  ->
                                          match uu___66_7626 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____7634 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____7634 with
                                               | (env1,uu____7646) ->
                                                   let uu____7651 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____7651 with
                                                    | (e1,uu____7663,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____7598
                                  FStar_List.unzip
                                 in
                              (match uu____7589 with
                               | (flags1,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___83_7702 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___83_7702.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___83_7702.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____7706 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u
                                        in
                                     match uu____7706 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let uu____7710 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____7710))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____7720 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____7721 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____7731 = aux u3  in FStar_Syntax_Syntax.U_succ uu____7731
        | FStar_Syntax_Syntax.U_max us ->
            let uu____7735 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____7735
        | FStar_Syntax_Syntax.U_name x ->
            let uu____7739 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____7739
            then u2
            else
              (let uu____7741 =
                 let uu____7742 =
                   let uu____7743 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.strcat uu____7743 " not found"  in
                 Prims.strcat "Universe variable " uu____7742  in
               failwith uu____7741)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____7745 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____7745 FStar_Pervasives_Native.snd
         | uu____7754 -> aux u)

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
            let uu____7783 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____7783 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____7889 bs2 bs_expected1 =
              match uu____7889 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____8057)) ->
                             let uu____8062 =
                               let uu____8067 =
                                 let uu____8068 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____8068
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____8067)
                                in
                             let uu____8069 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____8062 uu____8069
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____8070),FStar_Pervasives_Native.None ) ->
                             let uu____8075 =
                               let uu____8080 =
                                 let uu____8081 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____8081
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____8080)
                                in
                             let uu____8082 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____8075 uu____8082
                         | uu____8083 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____8089 =
                           let uu____8094 =
                             let uu____8095 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____8095.FStar_Syntax_Syntax.n  in
                           match uu____8094 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____8102 ->
                               ((let uu____8104 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____8104
                                 then
                                   let uu____8105 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____8105
                                 else ());
                                (let uu____8107 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____8107 with
                                 | (t,uu____8119,g1) ->
                                     let g2 =
                                       let uu____8122 =
                                         FStar_TypeChecker_Rel.teq_nosmt env2
                                           t expected_t
                                          in
                                       if uu____8122
                                       then
                                         FStar_TypeChecker_Rel.trivial_guard
                                       else
                                         (let uu____8124 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t
                                             in
                                          match uu____8124 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____8127 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t
                                                 in
                                              let uu____8132 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_Errors.raise_error
                                                uu____8127 uu____8132
                                          | FStar_Pervasives_Native.Some g2
                                              ->
                                              let uu____8134 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____8134
                                                "Type annotation on parameter incompatible with the expected type"
                                                g2)
                                        in
                                     let g3 =
                                       let uu____8136 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2
                                          in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____8136
                                        in
                                     (t, g3)))
                            in
                         match uu____8089 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___84_8164 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___84_8164.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___84_8164.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env3 = push_binding env2 b  in
                             let subst2 =
                               let uu____8177 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____8177
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
                  | uu____8331 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____8340 = tc_binders env1 bs  in
                  match uu____8340 with
                  | (bs1,envbody,g,uu____8370) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____8418 =
                    let uu____8419 = FStar_Syntax_Subst.compress t2  in
                    uu____8419.FStar_Syntax_Syntax.n  in
                  match uu____8418 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____8442 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8466 -> failwith "Impossible");
                       (let uu____8475 = tc_binders env1 bs  in
                        match uu____8475 with
                        | (bs1,envbody,g,uu____8507) ->
                            let uu____8508 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____8508 with
                             | (envbody1,uu____8536) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____8547;
                         FStar_Syntax_Syntax.pos = uu____8548;
                         FStar_Syntax_Syntax.vars = uu____8549;_},uu____8550)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8594 -> failwith "Impossible");
                       (let uu____8603 = tc_binders env1 bs  in
                        match uu____8603 with
                        | (bs1,envbody,g,uu____8635) ->
                            let uu____8636 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____8636 with
                             | (envbody1,uu____8664) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____8676) ->
                      let uu____8681 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____8681 with
                       | (uu____8722,bs1,bs',copt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____8765 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____8765 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____8888 c_expected2 body3
                               =
                               match uu____8888 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____9008 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env3, bs2, guard, uu____9008, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____9039 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____9039
                                           in
                                        let uu____9040 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env3, bs2, guard, uu____9040, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____9065 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____9065
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
                                               let uu____9117 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____9117 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____9140 =
                                                      check_binders env3
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____9140 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____9190 =
                                                           let uu____9221 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard'
                                                              in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____9221,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____9190
                                                           c_expected4 body3))
                                           | uu____9238 ->
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
                             let uu____9254 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____9254 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___85_9317 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___85_9317.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___85_9317.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___85_9317.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___85_9317.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___85_9317.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___85_9317.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___85_9317.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___85_9317.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___85_9317.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___85_9317.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___85_9317.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___85_9317.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___85_9317.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___85_9317.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___85_9317.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___85_9317.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___85_9317.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___85_9317.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___85_9317.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___85_9317.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___85_9317.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___85_9317.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___85_9317.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___85_9317.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___85_9317.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___85_9317.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___85_9317.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___85_9317.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___85_9317.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___85_9317.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___85_9317.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___85_9317.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___85_9317.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___85_9317.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___85_9317.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___85_9317.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____9365  ->
                                     fun uu____9366  ->
                                       match (uu____9365, uu____9366) with
                                       | ((env2,letrec_binders),(l,t3,u_names))
                                           ->
                                           let uu____9428 =
                                             let uu____9435 =
                                               let uu____9436 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2
                                                  in
                                               FStar_All.pipe_right
                                                 uu____9436
                                                 FStar_Pervasives_Native.fst
                                                in
                                             tc_term uu____9435 t3  in
                                           (match uu____9428 with
                                            | (t4,uu____9458,uu____9459) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (u_names, t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____9469 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___86_9472 =
                                                             x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___86_9472.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___86_9472.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____9469 ::
                                                        letrec_binders
                                                  | uu____9473 ->
                                                      letrec_binders
                                                   in
                                                (env3, lb))) (envbody1, []))
                              in
                           let uu____9478 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____9478 with
                            | (envbody,bs1,g,c,body2) ->
                                let uu____9532 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____9532 with
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
                  | uu____9578 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____9599 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2  in
                        as_function_typ true uu____9599
                      else
                        (let uu____9601 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____9601 with
                         | (uu____9640,bs1,uu____9642,c_opt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____9662 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____9662 with
          | (env1,topt) ->
              ((let uu____9682 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____9682
                then
                  let uu____9683 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____9683
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____9687 = expected_function_typ1 env1 topt body  in
                match uu____9687 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let uu____9727 =
                      let should_check_expected_effect =
                        let uu____9735 =
                          let uu____9742 =
                            let uu____9743 =
                              FStar_Syntax_Subst.compress body1  in
                            uu____9743.FStar_Syntax_Syntax.n  in
                          (c_opt, uu____9742)  in
                        match uu____9735 with
                        | (FStar_Pervasives_Native.None
                           ,FStar_Syntax_Syntax.Tm_ascribed
                           (uu____9748,(FStar_Util.Inr expected_c,uu____9750),uu____9751))
                            -> false
                        | uu____9800 -> true  in
                      let uu____9807 =
                        tc_term
                          (let uu___87_9816 = envbody  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___87_9816.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___87_9816.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___87_9816.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___87_9816.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___87_9816.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___87_9816.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___87_9816.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___87_9816.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___87_9816.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___87_9816.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___87_9816.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___87_9816.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___87_9816.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = false;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___87_9816.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq = use_eq;
                             FStar_TypeChecker_Env.is_iface =
                               (uu___87_9816.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___87_9816.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___87_9816.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___87_9816.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___87_9816.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___87_9816.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___87_9816.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___87_9816.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___87_9816.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___87_9816.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___87_9816.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___87_9816.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___87_9816.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___87_9816.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___87_9816.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___87_9816.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___87_9816.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___87_9816.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___87_9816.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___87_9816.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___87_9816.FStar_TypeChecker_Env.dep_graph)
                           }) body1
                         in
                      match uu____9807 with
                      | (body2,cbody,guard_body) ->
                          let guard_body1 =
                            FStar_TypeChecker_Rel.solve_deferred_constraints
                              envbody guard_body
                             in
                          if should_check_expected_effect
                          then
                            let uu____9833 =
                              let uu____9840 =
                                let uu____9845 =
                                  FStar_Syntax_Syntax.lcomp_comp cbody  in
                                (body2, uu____9845)  in
                              check_expected_effect
                                (let uu___88_9848 = envbody  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___88_9848.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___88_9848.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___88_9848.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___88_9848.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___88_9848.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___88_9848.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___88_9848.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___88_9848.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___88_9848.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___88_9848.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___88_9848.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___88_9848.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___88_9848.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___88_9848.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___88_9848.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___88_9848.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___88_9848.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___88_9848.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___88_9848.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___88_9848.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___88_9848.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___88_9848.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___88_9848.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___88_9848.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___88_9848.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___88_9848.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___88_9848.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___88_9848.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___88_9848.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___88_9848.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___88_9848.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___88_9848.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___88_9848.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___88_9848.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___88_9848.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___88_9848.FStar_TypeChecker_Env.dep_graph)
                                 }) c_opt uu____9840
                               in
                            (match uu____9833 with
                             | (body3,cbody1,guard) ->
                                 let uu____9858 =
                                   FStar_TypeChecker_Rel.conj_guard
                                     guard_body1 guard
                                    in
                                 (body3, cbody1, uu____9858))
                          else
                            (let uu____9860 =
                               FStar_Syntax_Syntax.lcomp_comp cbody  in
                             (body2, uu____9860, guard_body1))
                       in
                    (match uu____9727 with
                     | (body2,cbody,guard) ->
                         let guard1 =
                           let uu____9871 =
                             env1.FStar_TypeChecker_Env.top_level ||
                               (let uu____9873 =
                                  FStar_TypeChecker_Env.should_verify env1
                                   in
                                Prims.op_Negation uu____9873)
                              in
                           if uu____9871
                           then
                             let uu____9874 =
                               FStar_TypeChecker_Rel.conj_guard g guard  in
                             FStar_TypeChecker_Rel.discharge_guard envbody
                               uu____9874
                           else
                             (let guard1 =
                                let uu____9877 =
                                  FStar_TypeChecker_Rel.conj_guard g guard
                                   in
                                FStar_TypeChecker_Rel.close_guard env1
                                  (FStar_List.append bs1 letrec_binders)
                                  uu____9877
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
                         let uu____9886 =
                           match tfun_opt with
                           | FStar_Pervasives_Native.Some t ->
                               let t1 = FStar_Syntax_Subst.compress t  in
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_arrow uu____9907 ->
                                    (e, t1, guard1)
                                | uu____9920 ->
                                    let uu____9921 =
                                      FStar_TypeChecker_Util.check_and_ascribe
                                        env1 e tfun_computed t1
                                       in
                                    (match uu____9921 with
                                     | (e1,guard') ->
                                         let uu____9934 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 guard'
                                            in
                                         (e1, t1, uu____9934)))
                           | FStar_Pervasives_Native.None  ->
                               (e, tfun_computed, guard1)
                            in
                         (match uu____9886 with
                          | (e1,tfun,guard2) ->
                              let c = FStar_Syntax_Syntax.mk_Total tfun  in
                              let uu____9947 =
                                let uu____9952 =
                                  FStar_Syntax_Util.lcomp_of_comp c  in
                                FStar_TypeChecker_Util.strengthen_precondition
                                  FStar_Pervasives_Native.None env1 e1
                                  uu____9952 guard2
                                 in
                              (match uu____9947 with
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
              (let uu____9998 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____9998
               then
                 let uu____9999 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____10000 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____9999
                   uu____10000
               else ());
              (let monadic_application uu____10071 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____10071 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ
                        in
                     let cres1 =
                       let uu___89_10130 = cres  in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___89_10130.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___89_10130.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp_thunk =
                           (uu___89_10130.FStar_Syntax_Syntax.comp_thunk)
                       }  in
                     let uu____10131 =
                       match bs with
                       | [] ->
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard
                              in
                           (cres1, g)
                       | uu____10145 ->
                           let g =
                             let uu____10153 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard
                                in
                             FStar_All.pipe_right uu____10153
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env)
                              in
                           let uu____10154 =
                             let uu____10155 =
                               let uu____10158 =
                                 let uu____10159 =
                                   FStar_Syntax_Syntax.lcomp_comp cres1  in
                                 FStar_Syntax_Util.arrow bs uu____10159  in
                               FStar_Syntax_Syntax.mk_Total uu____10158  in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____10155
                              in
                           (uu____10154, g)
                        in
                     (match uu____10131 with
                      | (cres2,guard1) ->
                          ((let uu____10173 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low
                               in
                            if uu____10173
                            then
                              let uu____10174 =
                                FStar_Syntax_Print.lcomp_to_string cres2  in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____10174
                            else ());
                           (let cres3 =
                              let head_is_pure_and_some_arg_is_effectful =
                                (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                   chead1)
                                  &&
                                  (FStar_Util.for_some
                                     (fun uu____10190  ->
                                        match uu____10190 with
                                        | (uu____10199,uu____10200,lc) ->
                                            (let uu____10208 =
                                               FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                 lc
                                                in
                                             Prims.op_Negation uu____10208)
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
                              let uu____10218 =
                                (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                   cres2)
                                  && head_is_pure_and_some_arg_is_effectful
                                 in
                              if uu____10218
                              then
                                ((let uu____10220 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme
                                     in
                                  if uu____10220
                                  then
                                    let uu____10221 =
                                      FStar_Syntax_Print.term_to_string term
                                       in
                                    FStar_Util.print1
                                      "(a) Monadic app: Return inserted in monadic application: %s\n"
                                      uu____10221
                                  else ());
                                 FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                   env term cres2)
                              else
                                ((let uu____10225 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme
                                     in
                                  if uu____10225
                                  then
                                    let uu____10226 =
                                      FStar_Syntax_Print.term_to_string term
                                       in
                                    FStar_Util.print1
                                      "(a) Monadic app: No return inserted in monadic application: %s\n"
                                      uu____10226
                                  else ());
                                 cres2)
                               in
                            let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____10250  ->
                                     match uu____10250 with
                                     | ((e,q),x,c) ->
                                         ((let uu____10276 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____10276
                                           then
                                             let uu____10277 =
                                               match x with
                                               | FStar_Pervasives_Native.None
                                                    -> "_"
                                               | FStar_Pervasives_Native.Some
                                                   x1 ->
                                                   FStar_Syntax_Print.bv_to_string
                                                     x1
                                                in
                                             let uu____10279 =
                                               FStar_Syntax_Print.term_to_string
                                                 e
                                                in
                                             FStar_Util.print2
                                               "(b) Monadic app: Binding argument %s : %s\n"
                                               uu____10277 uu____10279
                                           else ());
                                          (let uu____10281 =
                                             FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                               c
                                              in
                                           if uu____10281
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
                              (let uu____10289 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme
                                  in
                               if uu____10289
                               then
                                 let uu____10290 =
                                   FStar_Syntax_Print.term_to_string head2
                                    in
                                 FStar_Util.print1
                                   "(c) Monadic app: Binding head %s "
                                   uu____10290
                               else ());
                              (let uu____10292 =
                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                   chead1
                                  in
                               if uu____10292
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
                              let uu____10300 =
                                let uu____10301 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____10301.FStar_Syntax_Syntax.n  in
                              match uu____10300 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____10305 -> false  in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____10326  ->
                                         match uu____10326 with
                                         | (arg,uu____10340,uu____10341) ->
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
                                (let uu____10351 =
                                   let map_fun uu____10415 =
                                     match uu____10415 with
                                     | ((e,q),uu____10450,c) ->
                                         let uu____10460 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c
                                            in
                                         if uu____10460
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
                                            let uu____10510 =
                                              let uu____10515 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              (uu____10515, q)  in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____10510))
                                      in
                                   let uu____10544 =
                                     let uu____10569 =
                                       let uu____10592 =
                                         let uu____10607 =
                                           let uu____10616 =
                                             FStar_Syntax_Syntax.as_arg head2
                                              in
                                           (uu____10616,
                                             FStar_Pervasives_Native.None,
                                             chead1)
                                            in
                                         uu____10607 :: arg_comps_rev  in
                                       FStar_List.map map_fun uu____10592  in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____10569
                                      in
                                   match uu____10544 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____10789 =
                                         let uu____10790 =
                                           FStar_List.hd reverse_args  in
                                         FStar_Pervasives_Native.fst
                                           uu____10790
                                          in
                                       let uu____10799 =
                                         let uu____10806 =
                                           FStar_List.tl reverse_args  in
                                         FStar_List.rev uu____10806  in
                                       (lifted_args, uu____10789,
                                         uu____10799)
                                    in
                                 match uu____10351 with
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
                                     let bind_lifted_args e uu___67_10913 =
                                       match uu___67_10913 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1
                                               [] e1.FStar_Syntax_Syntax.pos
                                              in
                                           let letbinding =
                                             let uu____10970 =
                                               let uu____10977 =
                                                 let uu____10978 =
                                                   let uu____10991 =
                                                     let uu____10992 =
                                                       let uu____10993 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x
                                                          in
                                                       [uu____10993]  in
                                                     FStar_Syntax_Subst.close
                                                       uu____10992 e
                                                      in
                                                   ((false, [lb]),
                                                     uu____10991)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____10978
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10977
                                                in
                                             uu____10970
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
                            let uu____11023 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp2
                                guard1
                               in
                            match uu____11023 with
                            | (comp3,g) ->
                                ((let uu____11040 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme
                                     in
                                  if uu____11040
                                  then
                                    let uu____11041 =
                                      FStar_Syntax_Print.term_to_string app
                                       in
                                    let uu____11042 =
                                      FStar_Syntax_Print.lcomp_to_string
                                        comp3
                                       in
                                    FStar_Util.print2
                                      "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                      uu____11041 uu____11042
                                  else ());
                                 (app, comp3, g)))))
                  in
               let rec tc_args head_info uu____11126 bs args1 =
                 match uu____11126 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____11269))::rest,
                         (uu____11271,FStar_Pervasives_Native.None )::uu____11272)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          let uu____11323 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____11323 with
                           | (varg,uu____11343,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1
                                  in
                               let arg =
                                 let uu____11365 =
                                   FStar_Syntax_Syntax.as_implicit true  in
                                 (varg, uu____11365)  in
                               let uu____11366 =
                                 let uu____11401 =
                                   let uu____11416 =
                                     let uu____11429 =
                                       let uu____11430 =
                                         FStar_Syntax_Syntax.mk_Total t1  in
                                       FStar_All.pipe_right uu____11430
                                         FStar_Syntax_Util.lcomp_of_comp
                                        in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____11429)
                                      in
                                   uu____11416 :: outargs  in
                                 let uu____11449 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g
                                    in
                                 (subst2, uu____11401, (arg :: arg_rets),
                                   uu____11449, fvs)
                                  in
                               tc_args head_info uu____11366 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____11541),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11542)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____11555 ->
                                let uu____11564 =
                                  let uu____11569 =
                                    let uu____11570 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____11571 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____11572 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____11573 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____11570 uu____11571 uu____11572
                                      uu____11573
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____11569)
                                   in
                                FStar_Errors.raise_error uu____11564
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x1 =
                              let uu___90_11576 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___90_11576.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___90_11576.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____11578 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____11578
                             then
                               let uu____11579 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____11579
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
                               let uu___91_11584 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___91_11584.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___91_11584.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___91_11584.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___91_11584.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___91_11584.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___91_11584.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___91_11584.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___91_11584.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___91_11584.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___91_11584.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___91_11584.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___91_11584.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___91_11584.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___91_11584.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___91_11584.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___91_11584.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___91_11584.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___91_11584.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___91_11584.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___91_11584.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___91_11584.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___91_11584.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___91_11584.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___91_11584.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___91_11584.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___91_11584.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___91_11584.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___91_11584.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___91_11584.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___91_11584.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___91_11584.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___91_11584.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___91_11584.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___91_11584.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___91_11584.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___91_11584.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             (let uu____11586 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High
                                 in
                              if uu____11586
                              then
                                let uu____11587 =
                                  FStar_Syntax_Print.tag_of_term e  in
                                let uu____11588 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____11589 =
                                  FStar_Syntax_Print.term_to_string targ1  in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____11587 uu____11588 uu____11589
                              else ());
                             (let uu____11591 = tc_term env2 e  in
                              match uu____11591 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e
                                     in
                                  let arg = (e1, aq)  in
                                  let xterm =
                                    let uu____11626 =
                                      let uu____11629 =
                                        let uu____11636 =
                                          FStar_Syntax_Syntax.bv_to_name x1
                                           in
                                        FStar_Syntax_Syntax.as_arg
                                          uu____11636
                                         in
                                      FStar_Pervasives_Native.fst uu____11629
                                       in
                                    (uu____11626, aq)  in
                                  let uu____11643 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name)
                                     in
                                  if uu____11643
                                  then
                                    let subst2 =
                                      let uu____11651 = FStar_List.hd bs  in
                                      maybe_extend_subst subst1 uu____11651
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
                      | (uu____11777,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____11809) ->
                          let uu____11852 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____11852 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____11890 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____11890
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____11915 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____11915 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            let uu____11937 =
                                              FStar_Syntax_Util.lcomp_of_comp
                                                cres'1
                                               in
                                            (head2, chead1, ghead1,
                                              uu____11937)
                                             in
                                          ((let uu____11939 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____11939
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
                                 | uu____11981 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2
                                          in
                                       let uu____11989 =
                                         let uu____11990 =
                                           FStar_Syntax_Subst.compress tres3
                                            in
                                         uu____11990.FStar_Syntax_Syntax.n
                                          in
                                       match uu____11989 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____11993;
                                              FStar_Syntax_Syntax.index =
                                                uu____11994;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},uu____11996)
                                           -> norm_tres tres4
                                       | uu____12003 -> tres3  in
                                     let uu____12004 = norm_tres tres1  in
                                     aux true uu____12004
                                 | uu____12005 ->
                                     let uu____12006 =
                                       let uu____12011 =
                                         let uu____12012 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead
                                            in
                                         let uu____12013 =
                                           FStar_Util.string_of_int n_args
                                            in
                                         FStar_Util.format2
                                           "Too many arguments to function of type %s; got %s arguments"
                                           uu____12012 uu____12013
                                          in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____12011)
                                        in
                                     let uu____12020 =
                                       FStar_Syntax_Syntax.argpos arg  in
                                     FStar_Errors.raise_error uu____12006
                                       uu____12020
                                  in
                               aux false chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app tf =
                 let uu____12039 =
                   let uu____12040 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____12040.FStar_Syntax_Syntax.n  in
                 match uu____12039 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____12049 ->
                     let bs =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun uu____12087  ->
                               let uu____12094 =
                                 let uu____12095 =
                                   let uu____12096 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_right uu____12096
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_TypeChecker_Util.new_uvar env
                                   uu____12095
                                  in
                               FStar_Syntax_Syntax.null_binder uu____12094))
                        in
                     let cres =
                       let t =
                         let uu____12107 =
                           let uu____12108 = FStar_Syntax_Util.type_u ()  in
                           FStar_All.pipe_right uu____12108
                             FStar_Pervasives_Native.fst
                            in
                         FStar_TypeChecker_Util.new_uvar env uu____12107  in
                       let uu____12117 = FStar_Options.ml_ish ()  in
                       if uu____12117
                       then FStar_Syntax_Util.ml_comp t r
                       else FStar_Syntax_Syntax.mk_Total t  in
                     let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                     ((let uu____12123 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           FStar_Options.Extreme
                          in
                       if uu____12123
                       then
                         let uu____12124 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____12125 =
                           FStar_Syntax_Print.term_to_string tf  in
                         let uu____12126 =
                           FStar_Syntax_Print.term_to_string bs_cres  in
                         FStar_Util.print3
                           "Forcing the type of %s from %s to %s\n"
                           uu____12124 uu____12125 uu____12126
                       else ());
                      (let uu____12129 =
                         FStar_TypeChecker_Rel.teq env tf bs_cres  in
                       FStar_All.pipe_left
                         (FStar_TypeChecker_Rel.force_trivial_guard env)
                         uu____12129);
                      check_function_app bs_cres)
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____12130;
                        FStar_Syntax_Syntax.pos = uu____12131;
                        FStar_Syntax_Syntax.vars = uu____12132;_},uu____12133)
                     ->
                     let bs =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun uu____12191  ->
                               let uu____12198 =
                                 let uu____12199 =
                                   let uu____12200 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_right uu____12200
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_TypeChecker_Util.new_uvar env
                                   uu____12199
                                  in
                               FStar_Syntax_Syntax.null_binder uu____12198))
                        in
                     let cres =
                       let t =
                         let uu____12211 =
                           let uu____12212 = FStar_Syntax_Util.type_u ()  in
                           FStar_All.pipe_right uu____12212
                             FStar_Pervasives_Native.fst
                            in
                         FStar_TypeChecker_Util.new_uvar env uu____12211  in
                       let uu____12221 = FStar_Options.ml_ish ()  in
                       if uu____12221
                       then FStar_Syntax_Util.ml_comp t r
                       else FStar_Syntax_Syntax.mk_Total t  in
                     let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                     ((let uu____12227 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           FStar_Options.Extreme
                          in
                       if uu____12227
                       then
                         let uu____12228 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____12229 =
                           FStar_Syntax_Print.term_to_string tf  in
                         let uu____12230 =
                           FStar_Syntax_Print.term_to_string bs_cres  in
                         FStar_Util.print3
                           "Forcing the type of %s from %s to %s\n"
                           uu____12228 uu____12229 uu____12230
                       else ());
                      (let uu____12233 =
                         FStar_TypeChecker_Rel.teq env tf bs_cres  in
                       FStar_All.pipe_left
                         (FStar_TypeChecker_Rel.force_trivial_guard env)
                         uu____12233);
                      check_function_app bs_cres)
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____12252 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____12252 with
                      | (bs1,c1) ->
                          let head_info =
                            let uu____12274 =
                              FStar_Syntax_Util.lcomp_of_comp c1  in
                            (head1, chead, ghead, uu____12274)  in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____12316) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____12322,uu____12323) -> check_function_app t
                 | uu____12364 ->
                     let uu____12365 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____12365
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
                  let uu____12437 =
                    FStar_List.fold_left2
                      (fun uu____12480  ->
                         fun uu____12481  ->
                           fun uu____12482  ->
                             match (uu____12480, uu____12481, uu____12482)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                        "Inconsistent implicit qualifiers")
                                      e.FStar_Syntax_Syntax.pos
                                  else ();
                                  (let uu____12550 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____12550 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____12568 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____12568 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____12572 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____12572)
                                              &&
                                              (let uu____12574 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____12574))
                                          in
                                       let uu____12575 =
                                         let uu____12584 =
                                           let uu____12593 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____12593]  in
                                         FStar_List.append seen uu____12584
                                          in
                                       let uu____12600 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1
                                          in
                                       (uu____12575, uu____12600, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____12437 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____12636 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____12636
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____12638 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____12638 with | (c2,g) -> (e, c2, g)))
              | uu____12656 ->
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
        let uu____12699 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____12699 with
        | (pattern,when_clause,branch_exp) ->
            let uu____12744 = branch1  in
            (match uu____12744 with
             | (cpat,uu____12785,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let tc_annot env1 t =
                     let uu____12862 = FStar_Syntax_Util.type_u ()  in
                     match uu____12862 with
                     | (tu,u) ->
                         let uu____12873 =
                           tc_check_tot_or_gtot_term env1 t tu  in
                         (match uu____12873 with
                          | (t1,uu____12885,g) -> (t1, g))
                      in
                   let uu____12887 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0
                       tc_annot
                      in
                   match uu____12887 with
                   | (pat_bvs1,exp,guard_pat_annots,p) ->
                       ((let uu____12921 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         if uu____12921
                         then
                           let uu____12922 =
                             FStar_Syntax_Print.pat_to_string p0  in
                           let uu____12923 =
                             FStar_Syntax_Print.pat_to_string p  in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____12922 uu____12923
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1
                            in
                         let uu____12926 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env
                            in
                         match uu____12926 with
                         | (env1,uu____12948) ->
                             let env11 =
                               let uu___92_12954 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___92_12954.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___92_12954.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___92_12954.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___92_12954.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___92_12954.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___92_12954.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___92_12954.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___92_12954.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___92_12954.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___92_12954.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___92_12954.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___92_12954.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___92_12954.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___92_12954.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___92_12954.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___92_12954.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___92_12954.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___92_12954.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___92_12954.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___92_12954.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___92_12954.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___92_12954.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___92_12954.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___92_12954.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___92_12954.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___92_12954.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___92_12954.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___92_12954.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___92_12954.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___92_12954.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___92_12954.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___92_12954.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___92_12954.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___92_12954.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___92_12954.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___92_12954.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t  in
                             ((let uu____12957 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High
                                  in
                               if uu____12957
                               then
                                 let uu____12958 =
                                   FStar_Syntax_Print.term_to_string exp  in
                                 let uu____12959 =
                                   FStar_Syntax_Print.term_to_string pat_t
                                    in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____12958 uu____12959
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t
                                  in
                               let uu____12962 =
                                 tc_tot_or_gtot_term env12 exp  in
                               match uu____12962 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___93_12987 = g  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___93_12987.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___93_12987.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___93_12987.FStar_TypeChecker_Env.implicits)
                                     }  in
                                   let uu____12988 =
                                     let uu____12989 =
                                       FStar_TypeChecker_Rel.teq_nosmt env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t
                                        in
                                     if uu____12989
                                     then
                                       let env13 =
                                         FStar_TypeChecker_Env.set_range
                                           env12 exp1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____12991 =
                                         FStar_TypeChecker_Rel.discharge_guard_no_smt
                                           env13 g1
                                          in
                                       FStar_All.pipe_right uu____12991
                                         FStar_TypeChecker_Rel.resolve_implicits
                                     else
                                       (let uu____12993 =
                                          let uu____12998 =
                                            let uu____12999 =
                                              FStar_Syntax_Print.term_to_string
                                                lc.FStar_Syntax_Syntax.res_typ
                                               in
                                            let uu____13000 =
                                              FStar_Syntax_Print.term_to_string
                                                expected_pat_t
                                               in
                                            FStar_Util.format2
                                              "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                              uu____12999 uu____13000
                                             in
                                          (FStar_Errors.Fatal_MismatchedPatternType,
                                            uu____12998)
                                           in
                                        FStar_Errors.raise_error uu____12993
                                          exp1.FStar_Syntax_Syntax.pos)
                                      in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1
                                      in
                                   let uvs_to_string uvs =
                                     let uu____13020 =
                                       let uu____13023 =
                                         FStar_Util.set_elements uvs  in
                                       FStar_All.pipe_right uu____13023
                                         (FStar_List.map
                                            (fun uu____13049  ->
                                               match uu____13049 with
                                               | (u,uu____13055) ->
                                                   FStar_Syntax_Print.uvar_to_string
                                                     u))
                                        in
                                     FStar_All.pipe_right uu____13020
                                       (FStar_String.concat ", ")
                                      in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp  in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t
                                      in
                                   ((let uu____13073 =
                                       FStar_TypeChecker_Env.debug env
                                         (FStar_Options.Other "Free")
                                        in
                                     if uu____13073
                                     then
                                       ((let uu____13075 =
                                           FStar_Syntax_Print.term_to_string
                                             norm_exp
                                            in
                                         let uu____13076 = uvs_to_string uvs1
                                            in
                                         FStar_Util.print2
                                           ">> free_1(%s) = %s\n" uu____13075
                                           uu____13076);
                                        (let uu____13077 =
                                           FStar_Syntax_Print.term_to_string
                                             expected_pat_t
                                            in
                                         let uu____13078 = uvs_to_string uvs2
                                            in
                                         FStar_Util.print2
                                           ">> free_2(%s) = %s\n" uu____13077
                                           uu____13078))
                                     else ());
                                    (let uu____13081 =
                                       let uu____13082 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2
                                          in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____13082
                                        in
                                     if uu____13081
                                     then
                                       let unresolved =
                                         FStar_Util.set_difference uvs1 uvs2
                                          in
                                       let uu____13098 =
                                         let uu____13103 =
                                           let uu____13104 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env norm_exp
                                              in
                                           let uu____13105 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env expected_pat_t
                                              in
                                           let uu____13106 =
                                             uvs_to_string unresolved  in
                                           FStar_Util.format3
                                             "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                             uu____13104 uu____13105
                                             uu____13106
                                            in
                                         (FStar_Errors.Fatal_UnresolvedPatternVar,
                                           uu____13103)
                                          in
                                       FStar_Errors.raise_error uu____13098
                                         p.FStar_Syntax_Syntax.p
                                     else ());
                                    (let uu____13109 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High
                                        in
                                     if uu____13109
                                     then
                                       let uu____13110 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1
                                          in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____13110
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
                 let uu____13119 =
                   let uu____13126 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____13126
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____13119 with
                  | (scrutinee_env,uu____13159) ->
                      let uu____13164 = tc_pat true pat_t pattern  in
                      (match uu____13164 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,guard_pat_annots,norm_pat_exp)
                           ->
                           let uu____13214 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____13236 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____13236
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____13250 =
                                      let uu____13257 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____13257 e  in
                                    match uu____13250 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____13214 with
                            | (when_clause1,g_when) ->
                                let uu____13300 = tc_term pat_env branch_exp
                                   in
                                (match uu____13300 with
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
                                           let uu____13342 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_18  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_18) uu____13342
                                        in
                                     let uu____13345 =
                                       let eqs =
                                         let uu____13364 =
                                           let uu____13365 =
                                             FStar_TypeChecker_Env.should_verify
                                               env
                                              in
                                           Prims.op_Negation uu____13365  in
                                         if uu____13364
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp
                                               in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____13372 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____13389 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____13390 ->
                                                FStar_Pervasives_Native.None
                                            | uu____13391 ->
                                                let uu____13392 =
                                                  let uu____13393 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____13393 pat_t
                                                    scrutinee_tm e
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____13392)
                                          in
                                       let uu____13394 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch1
                                          in
                                       match uu____13394 with
                                       | (c1,g_branch2) ->
                                           let uu____13419 =
                                             match (eqs, when_condition) with
                                             | uu____13432 when
                                                 let uu____13441 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation
                                                   uu____13441
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
                                                 let uu____13453 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf
                                                    in
                                                 let uu____13454 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when
                                                    in
                                                 (uu____13453, uu____13454)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g_fw =
                                                   let uu____13463 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w
                                                      in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____13463
                                                    in
                                                 let uu____13464 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw
                                                    in
                                                 let uu____13465 =
                                                   let uu____13466 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f
                                                      in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____13466 g_when
                                                    in
                                                 (uu____13464, uu____13465)
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
                                                 let uu____13474 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w
                                                    in
                                                 (uu____13474, g_when)
                                              in
                                           (match uu____13419 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1
                                                   in
                                                let maybe_return_c_weak
                                                  should_return =
                                                  let c_weak1 =
                                                    let uu____13502 =
                                                      should_return &&
                                                        (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                           c_weak)
                                                       in
                                                    if uu____13502
                                                    then
                                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                        env branch_exp1
                                                        c_weak
                                                    else c_weak  in
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak1
                                                   in
                                                let uu____13504 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak
                                                   in
                                                ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                  (c_weak.FStar_Syntax_Syntax.cflags),
                                                  maybe_return_c_weak,
                                                  uu____13504, g_branch2))
                                        in
                                     (match uu____13345 with
                                      | (effect_label,cflags,maybe_return_c,g_when1,g_branch2)
                                          ->
                                          let branch_guard =
                                            let uu____13551 =
                                              let uu____13552 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____13552
                                               in
                                            if uu____13551
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____13590 =
                                                     let uu____13591 =
                                                       let uu____13592 =
                                                         let uu____13595 =
                                                           let uu____13602 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v
                                                              in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____13602
                                                            in
                                                         FStar_Pervasives_Native.snd
                                                           uu____13595
                                                          in
                                                       FStar_List.length
                                                         uu____13592
                                                        in
                                                     uu____13591 >
                                                       (Prims.parse_int "1")
                                                      in
                                                   if uu____13590
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     let uu____13608 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator
                                                        in
                                                     match uu____13608 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____13629 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         let disc1 =
                                                           let uu____13644 =
                                                             let uu____13649
                                                               =
                                                               let uu____13650
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2
                                                                  in
                                                               [uu____13650]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____13649
                                                              in
                                                           uu____13644
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                            in
                                                         let uu____13653 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool
                                                            in
                                                         [uu____13653]
                                                   else []  in
                                                 let fail1 uu____13660 =
                                                   let uu____13661 =
                                                     let uu____13662 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos
                                                        in
                                                     let uu____13663 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1
                                                        in
                                                     let uu____13664 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1
                                                        in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____13662
                                                       uu____13663
                                                       uu____13664
                                                      in
                                                   failwith uu____13661  in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____13677) ->
                                                       head_constructor t1
                                                   | uu____13682 -> fail1 ()
                                                    in
                                                 let pat_exp2 =
                                                   let uu____13684 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____13684
                                                     FStar_Syntax_Util.unmeta
                                                    in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____13687 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____13704;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____13705;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____13706;_},uu____13707)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____13744 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c1 ->
                                                     let uu____13746 =
                                                       let uu____13747 =
                                                         tc_constant env
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c1
                                                          in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____13747
                                                         scrutinee_tm1
                                                         pat_exp2
                                                        in
                                                     [uu____13746]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____13748 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____13756 =
                                                       let uu____13757 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____13757
                                                        in
                                                     if uu____13756
                                                     then []
                                                     else
                                                       (let uu____13761 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13761)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____13764 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____13766 =
                                                       let uu____13767 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____13767
                                                        in
                                                     if uu____13766
                                                     then []
                                                     else
                                                       (let uu____13771 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13771)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1
                                                        in
                                                     let uu____13797 =
                                                       let uu____13798 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____13798
                                                        in
                                                     if uu____13797
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____13805 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____13837
                                                                     ->
                                                                    match uu____13837
                                                                    with
                                                                    | 
                                                                    (ei,uu____13847)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____13853
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____13853
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____13874
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____13888
                                                                    =
                                                                    let uu____13893
                                                                    =
                                                                    let uu____13894
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____13894
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____13895
                                                                    =
                                                                    let uu____13896
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1
                                                                     in
                                                                    [uu____13896]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____13893
                                                                    uu____13895
                                                                     in
                                                                    uu____13888
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13805
                                                            FStar_List.flatten
                                                           in
                                                        let uu____13905 =
                                                          discriminate
                                                            scrutinee_tm1 f
                                                           in
                                                        FStar_List.append
                                                          uu____13905
                                                          sub_term_guards)
                                                 | uu____13908 -> []  in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____13924 =
                                                   let uu____13925 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____13925
                                                    in
                                                 if uu____13924
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____13928 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____13928
                                                       in
                                                    let uu____13933 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    match uu____13933 with
                                                    | (k,uu____13939) ->
                                                        let uu____13940 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k
                                                           in
                                                        (match uu____13940
                                                         with
                                                         | (t1,uu____13948,uu____13949)
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
                                          ((let uu____13955 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High
                                               in
                                            if uu____13955
                                            then
                                              let uu____13956 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard
                                                 in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____13956
                                            else ());
                                           (let uu____13958 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1)
                                               in
                                            (uu____13958, branch_guard,
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
          let uu____13989 = check_let_bound_def true env1 lb  in
          (match uu____13989 with
           | (e1,univ_vars1,c1,g1,topt) ->
               let uu____14017 =
                 if
                   (FStar_Util.is_some topt) &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____14034 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____14034, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____14037 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____14037
                        FStar_TypeChecker_Rel.resolve_implicits
                       in
                    let uu____14039 =
                      let uu____14052 =
                        let uu____14067 =
                          let uu____14076 =
                            let uu____14087 =
                              FStar_Syntax_Syntax.lcomp_comp c1  in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____14087)
                             in
                          [uu____14076]  in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____14067
                         in
                      FStar_List.hd uu____14052  in
                    match uu____14039 with
                    | (uu____14132,univs1,e11,c11,gvs) ->
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
                        let uu____14146 = FStar_Syntax_Util.lcomp_of_comp c11
                           in
                        (g13, e11, univs1, uu____14146))
                  in
               (match uu____14017 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____14157 =
                      let uu____14164 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____14164
                      then
                        let uu____14171 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____14171 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____14194 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____14194
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____14195 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____14195, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____14205 =
                              FStar_Syntax_Syntax.lcomp_comp c11  in
                            FStar_All.pipe_right uu____14205
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm;
                                 FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]
                                 env1)
                             in
                          let e21 =
                            let uu____14209 =
                              FStar_Syntax_Util.is_pure_comp c  in
                            if uu____14209
                            then e2
                            else
                              ((let uu____14214 =
                                  FStar_TypeChecker_Env.get_range env1  in
                                FStar_Errors.log_issue uu____14214
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
                    (match uu____14157 with
                     | (e21,c12) ->
                         let cres =
                           FStar_TypeChecker_Env.null_wp_for_eff env1
                             (FStar_Syntax_Util.comp_effect_name c12)
                             FStar_Syntax_Syntax.U_zero
                             FStar_Syntax_Syntax.t_unit
                            in
                         let lb1 =
                           let uu____14233 =
                             if FStar_Util.is_some topt
                             then FStar_All.pipe_right topt FStar_Util.must
                             else FStar_Syntax_Util.comp_result c12  in
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             lb.FStar_Syntax_Syntax.lbname univ_vars2
                             uu____14233
                             (FStar_Syntax_Util.comp_effect_name c12) e11
                             lb.FStar_Syntax_Syntax.lbattrs
                             lb.FStar_Syntax_Syntax.lbpos
                            in
                         let uu____14239 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos
                            in
                         let uu____14252 =
                           FStar_Syntax_Util.lcomp_of_comp cres  in
                         (uu____14239, uu____14252,
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____14255 -> failwith "Impossible"

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
            let uu___94_14286 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___94_14286.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___94_14286.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___94_14286.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___94_14286.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___94_14286.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___94_14286.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___94_14286.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___94_14286.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___94_14286.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___94_14286.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___94_14286.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___94_14286.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___94_14286.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___94_14286.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___94_14286.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___94_14286.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___94_14286.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___94_14286.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___94_14286.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___94_14286.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___94_14286.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___94_14286.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___94_14286.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___94_14286.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___94_14286.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___94_14286.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___94_14286.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___94_14286.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___94_14286.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___94_14286.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___94_14286.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___94_14286.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___94_14286.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___94_14286.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___94_14286.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___94_14286.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____14287 =
            let uu____14300 =
              let uu____14301 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____14301 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____14300 lb  in
          (match uu____14287 with
           | (e1,uu____14323,c1,g1,annotated) ->
               ((let uu____14332 =
                   (FStar_Util.for_some
                      (FStar_Syntax_Util.is_fvar
                         FStar_Parser_Const.inline_let_attr)
                      lb.FStar_Syntax_Syntax.lbattrs)
                     &&
                     (let uu____14334 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp c1  in
                      Prims.op_Negation uu____14334)
                    in
                 if uu____14332
                 then
                   let uu____14335 =
                     let uu____14340 =
                       let uu____14341 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____14342 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____14341 uu____14342
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____14340)
                      in
                   FStar_Errors.raise_error uu____14335
                     e1.FStar_Syntax_Syntax.pos
                 else ());
                (let x =
                   let uu___95_14345 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___95_14345.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___95_14345.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_Syntax_Syntax.res_typ)
                   }  in
                 let uu____14346 =
                   let uu____14351 =
                     let uu____14352 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____14352]  in
                   FStar_Syntax_Subst.open_term uu____14351 e2  in
                 match uu____14346 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____14372 = tc_term env_x e21  in
                     (match uu____14372 with
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
                            let uu____14397 =
                              let uu____14404 =
                                let uu____14405 =
                                  let uu____14418 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____14418)  in
                                FStar_Syntax_Syntax.Tm_let uu____14405  in
                              FStar_Syntax_Syntax.mk uu____14404  in
                            uu____14397 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.res_typ
                             in
                          let x_eq_e1 =
                            let uu____14432 =
                              let uu____14433 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_Syntax_Syntax.res_typ
                                 in
                              let uu____14434 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____14433
                                c1.FStar_Syntax_Syntax.res_typ uu____14434
                                e11
                               in
                            FStar_All.pipe_left
                              (fun _0_19  ->
                                 FStar_TypeChecker_Common.NonTrivial _0_19)
                              uu____14432
                             in
                          let g21 =
                            let uu____14436 =
                              let uu____14437 =
                                FStar_TypeChecker_Rel.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Rel.imp_guard uu____14437 g2
                               in
                            FStar_TypeChecker_Rel.close_guard env2 xb
                              uu____14436
                             in
                          let guard = FStar_TypeChecker_Rel.conj_guard g1 g21
                             in
                          let uu____14439 =
                            let uu____14440 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____14440  in
                          if uu____14439
                          then
                            let tt =
                              let uu____14450 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____14450
                                FStar_Option.get
                               in
                            ((let uu____14456 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____14456
                              then
                                let uu____14457 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____14458 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____14457 uu____14458
                              else ());
                             (e4, cres, guard))
                          else
                            (let t =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1] cres.FStar_Syntax_Syntax.res_typ
                                in
                             (let uu____14463 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____14463
                              then
                                let uu____14464 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____14465 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "Checked %s has no escaping types; normalized to %s\n"
                                  uu____14464 uu____14465
                              else ());
                             (e4,
                               ((let uu___96_14468 = cres  in
                                 {
                                   FStar_Syntax_Syntax.eff_name =
                                     (uu___96_14468.FStar_Syntax_Syntax.eff_name);
                                   FStar_Syntax_Syntax.res_typ = t;
                                   FStar_Syntax_Syntax.cflags =
                                     (uu___96_14468.FStar_Syntax_Syntax.cflags);
                                   FStar_Syntax_Syntax.comp_thunk =
                                     (uu___96_14468.FStar_Syntax_Syntax.comp_thunk)
                                 })), guard))))))
      | uu____14469 -> failwith "Impossible"

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
          let uu____14501 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____14501 with
           | (lbs1,e21) ->
               let uu____14520 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____14520 with
                | (env0,topt) ->
                    let uu____14539 = build_let_rec_env true env0 lbs1  in
                    (match uu____14539 with
                     | (lbs2,rec_env) ->
                         let uu____14558 = check_let_recs rec_env lbs2  in
                         (match uu____14558 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____14578 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs
                                   in
                                FStar_All.pipe_right uu____14578
                                  FStar_TypeChecker_Rel.resolve_implicits
                                 in
                              let all_lb_names =
                                let uu____14584 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____14584
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
                                     let uu____14633 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____14673 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____14673)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____14633
                                      in
                                   FStar_List.map2
                                     (fun uu____14707  ->
                                        fun lb  ->
                                          match uu____14707 with
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
                                let uu____14755 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____14755
                                 in
                              let uu____14760 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____14760 with
                               | (lbs5,e22) ->
                                   ((let uu____14780 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____14780
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____14781 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____14781, cres,
                                       FStar_TypeChecker_Rel.trivial_guard))))))))
      | uu____14794 -> failwith "Impossible"

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
          let uu____14826 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____14826 with
           | (lbs1,e21) ->
               let uu____14845 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____14845 with
                | (env0,topt) ->
                    let uu____14864 = build_let_rec_env false env0 lbs1  in
                    (match uu____14864 with
                     | (lbs2,rec_env) ->
                         let uu____14883 = check_let_recs rec_env lbs2  in
                         (match uu____14883 with
                          | (lbs3,g_lbs) ->
                              let uu____14902 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___97_14925 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___97_14925.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___97_14925.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___98_14927 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___98_14927.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___98_14927.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___98_14927.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___98_14927.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___98_14927.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___98_14927.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____14902 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____14954 = tc_term env2 e21  in
                                   (match uu____14954 with
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
                                          let uu____14973 =
                                            let uu____14974 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____14974 g2
                                             in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____14973
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
                                          let uu___99_14978 = cres3  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___99_14978.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___99_14978.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___99_14978.FStar_Syntax_Syntax.comp_thunk)
                                          }  in
                                        let uu____14979 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____14979 with
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
                                                  uu____15015 ->
                                                  (e, cres4, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  let cres5 =
                                                    let uu___100_15020 =
                                                      cres4  in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___100_15020.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___100_15020.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp_thunk
                                                        =
                                                        (uu___100_15020.FStar_Syntax_Syntax.comp_thunk)
                                                    }  in
                                                  (e, cres5, guard)))))))))
      | uu____15023 -> failwith "Impossible"

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
          let uu____15058 = FStar_Options.ml_ish ()  in
          if uu____15058
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____15061 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____15061 with
             | (formals,c) ->
                 let uu____15086 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____15086 with
                  | (actuals,uu____15096,uu____15097) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____15110 =
                          let uu____15115 =
                            let uu____15116 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____15117 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____15116 uu____15117
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____15115)
                           in
                        FStar_Errors.raise_error uu____15110
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____15120 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____15120 actuals
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
                                (let uu____15141 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____15141)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____15159 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____15159)
                               in
                            let msg =
                              let uu____15167 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____15168 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____15167 uu____15168 formals_msg
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
        let uu____15175 =
          FStar_List.fold_left
            (fun uu____15201  ->
               fun lb  ->
                 match uu____15201 with
                 | (lbs1,env1) ->
                     let uu____15221 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____15221 with
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
                               let uu____15242 =
                                 let uu____15249 =
                                   let uu____15250 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____15250
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___101_15261 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___101_15261.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___101_15261.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___101_15261.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___101_15261.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___101_15261.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___101_15261.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___101_15261.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___101_15261.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___101_15261.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___101_15261.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___101_15261.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___101_15261.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___101_15261.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___101_15261.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___101_15261.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___101_15261.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___101_15261.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___101_15261.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___101_15261.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___101_15261.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___101_15261.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___101_15261.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___101_15261.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___101_15261.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___101_15261.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___101_15261.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___101_15261.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___101_15261.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___101_15261.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___101_15261.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___101_15261.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___101_15261.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___101_15261.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___101_15261.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___101_15261.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___101_15261.FStar_TypeChecker_Env.dep_graph)
                                    }) t uu____15249
                                  in
                               match uu____15242 with
                               | (t1,uu____15263,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g
                                      in
                                   ((let uu____15267 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1
                                        in
                                     FStar_All.pipe_left (fun a239  -> ())
                                       uu____15267);
                                    norm env01 t1))
                             in
                          let env3 =
                            let uu____15269 =
                              termination_check_enabled
                                lb.FStar_Syntax_Syntax.lbname e t1
                               in
                            if uu____15269
                            then
                              let uu___102_15270 = env2  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___102_15270.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___102_15270.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___102_15270.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___102_15270.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___102_15270.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___102_15270.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___102_15270.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___102_15270.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___102_15270.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___102_15270.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___102_15270.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___102_15270.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1,
                                     univ_vars1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___102_15270.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___102_15270.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___102_15270.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___102_15270.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___102_15270.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___102_15270.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___102_15270.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___102_15270.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___102_15270.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___102_15270.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___102_15270.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___102_15270.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___102_15270.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___102_15270.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___102_15270.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___102_15270.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___102_15270.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___102_15270.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___102_15270.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___102_15270.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___102_15270.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___102_15270.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___102_15270.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___102_15270.FStar_TypeChecker_Env.dep_graph)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname
                                (univ_vars1, t1)
                             in
                          let lb1 =
                            let uu___103_15287 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___103_15287.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___103_15287.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___103_15287.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___103_15287.FStar_Syntax_Syntax.lbpos)
                            }  in
                          ((lb1 :: lbs1), env3))) ([], env) lbs
           in
        match uu____15175 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lbs  ->
      let uu____15310 =
        let uu____15319 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____15345 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____15345 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____15373 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____15373
                       | uu____15378 ->
                           let lb1 =
                             let uu___104_15381 = lb  in
                             let uu____15382 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___104_15381.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___104_15381.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___104_15381.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___104_15381.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____15382;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___104_15381.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___104_15381.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____15385 =
                             let uu____15392 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____15392
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____15385 with
                            | (e,c,g) ->
                                ((let uu____15401 =
                                    let uu____15402 =
                                      FStar_Syntax_Util.is_total_lcomp c  in
                                    Prims.op_Negation uu____15402  in
                                  if uu____15401
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
        FStar_All.pipe_right uu____15319 FStar_List.unzip  in
      match uu____15310 with
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
          FStar_TypeChecker_Env.guard_t,FStar_Syntax_Syntax.typ
                                          FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple5)
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let uu____15453 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____15453 with
        | (env1,uu____15473) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____15481 = check_lbtyp top_level env lb  in
            (match uu____15481 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____15525 =
                     tc_maybe_toplevel_term
                       (let uu___105_15534 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___105_15534.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___105_15534.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___105_15534.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___105_15534.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___105_15534.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___105_15534.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___105_15534.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___105_15534.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___105_15534.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___105_15534.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___105_15534.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___105_15534.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___105_15534.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___105_15534.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___105_15534.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___105_15534.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___105_15534.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___105_15534.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___105_15534.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.failhard =
                            (uu___105_15534.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___105_15534.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___105_15534.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___105_15534.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___105_15534.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___105_15534.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___105_15534.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___105_15534.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___105_15534.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___105_15534.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___105_15534.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___105_15534.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___105_15534.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___105_15534.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___105_15534.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___105_15534.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___105_15534.FStar_TypeChecker_Env.dep_graph)
                        }) e11
                      in
                   match uu____15525 with
                   | (e12,c1,g1) ->
                       let uu____15550 =
                         let uu____15555 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____15560  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____15555 e12 c1 wf_annot
                          in
                       (match uu____15550 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f  in
                            ((let uu____15577 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____15577
                              then
                                let uu____15578 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____15579 =
                                  FStar_Syntax_Print.lcomp_to_string c11  in
                                let uu____15580 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____15578 uu____15579 uu____15580
                              else ());
                             (e12, univ_vars1, c11, g11, topt))))))

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
            let uu____15616 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____15616 with
             | (univ_opening,univ_vars1) ->
                 let uu____15649 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                   univ_opening, uu____15649))
        | uu____15656 ->
            let uu____15657 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____15657 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____15706 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____15706)
                 else
                   (let uu____15714 = FStar_Syntax_Util.type_u ()  in
                    match uu____15714 with
                    | (k,uu____15734) ->
                        let uu____15735 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____15735 with
                         | (t2,uu____15757,g) ->
                             ((let uu____15760 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____15760
                               then
                                 let uu____15761 =
                                   let uu____15762 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____15762
                                    in
                                 let uu____15763 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____15761 uu____15763
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____15766 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____15766))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun uu____15774  ->
      match uu____15774 with
      | (x,imp) ->
          let uu____15793 = FStar_Syntax_Util.type_u ()  in
          (match uu____15793 with
           | (tu,u) ->
               ((let uu____15813 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____15813
                 then
                   let uu____15814 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____15815 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____15816 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____15814 uu____15815 uu____15816
                 else ());
                (let uu____15818 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____15818 with
                 | (t,uu____15838,g) ->
                     let x1 =
                       ((let uu___106_15846 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___106_15846.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___106_15846.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____15848 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       if uu____15848
                       then
                         let uu____15849 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1)
                            in
                         let uu____15850 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____15849 uu____15850
                       else ());
                      (let uu____15852 = push_binding env x1  in
                       (x1, uu____15852, g, u))))))

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
            let uu____15946 = tc_binder env1 b  in
            (match uu____15946 with
             | (b1,env',g,u) ->
                 let uu____15987 = aux env' bs2  in
                 (match uu____15987 with
                  | (bs3,env'1,g',us) ->
                      let uu____16040 =
                        let uu____16041 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g'
                           in
                        FStar_TypeChecker_Rel.conj_guard g uu____16041  in
                      ((b1 :: bs3), env'1, uu____16040, (u :: us))))
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
          (fun uu____16130  ->
             fun uu____16131  ->
               match (uu____16130, uu____16131) with
               | ((t,imp),(args1,g)) ->
                   let uu____16200 = tc_term env1 t  in
                   (match uu____16200 with
                    | (t1,uu____16218,g') ->
                        let uu____16220 =
                          FStar_TypeChecker_Rel.conj_guard g g'  in
                        (((t1, imp) :: args1), uu____16220))) args
          ([], FStar_TypeChecker_Rel.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____16262  ->
             match uu____16262 with
             | (pats1,g) ->
                 let uu____16287 = tc_args env p  in
                 (match uu____16287 with
                  | (args,g') ->
                      let uu____16300 = FStar_TypeChecker_Rel.conj_guard g g'
                         in
                      ((args :: pats1), uu____16300))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let uu____16313 = tc_maybe_toplevel_term env e  in
      match uu____16313 with
      | (e1,c,g) ->
          let uu____16329 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____16329
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c  in
             let c2 = norm_c env c1  in
             let uu____16340 =
               let uu____16345 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____16345
               then
                 let uu____16350 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____16350, false)
               else
                 (let uu____16352 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____16352, true))
                in
             match uu____16340 with
             | (target_comp,allow_ghost) ->
                 let uu____16361 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____16361 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____16371 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp  in
                      let uu____16372 =
                        FStar_TypeChecker_Rel.conj_guard g1 g'  in
                      (e1, uu____16371, uu____16372)
                  | uu____16373 ->
                      if allow_ghost
                      then
                        let uu____16382 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2
                           in
                        FStar_Errors.raise_error uu____16382
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____16394 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2
                            in
                         FStar_Errors.raise_error uu____16394
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
      let uu____16417 = tc_tot_or_gtot_term env t  in
      match uu____16417 with
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
      (let uu____16449 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____16449
       then
         let uu____16450 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____16450
       else ());
      (let env1 =
         let uu___107_16453 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___107_16453.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___107_16453.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___107_16453.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___107_16453.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___107_16453.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___107_16453.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___107_16453.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___107_16453.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___107_16453.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___107_16453.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___107_16453.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___107_16453.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___107_16453.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___107_16453.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___107_16453.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___107_16453.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___107_16453.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___107_16453.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___107_16453.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___107_16453.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___107_16453.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___107_16453.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___107_16453.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___107_16453.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___107_16453.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___107_16453.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___107_16453.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.proof_ns =
             (uu___107_16453.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___107_16453.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___107_16453.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___107_16453.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___107_16453.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___107_16453.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___107_16453.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___107_16453.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____16460 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (e1,msg,uu____16495) ->
             let uu____16496 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____16496
          in
       match uu____16460 with
       | (t,c,g) ->
           let uu____16512 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____16512
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____16522 =
                let uu____16527 =
                  let uu____16528 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____16528
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____16527)
                 in
              let uu____16529 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____16522 uu____16529))
  
let level_of_type_fail :
  'Auu____16544 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____16544
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____16560 =
          let uu____16565 =
            let uu____16566 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____16566 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____16565)  in
        let uu____16567 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____16560 uu____16567
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____16594 =
            let uu____16595 = FStar_Syntax_Util.unrefine t1  in
            uu____16595.FStar_Syntax_Syntax.n  in
          match uu____16594 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____16599 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____16602 = FStar_Syntax_Util.type_u ()  in
                 match uu____16602 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___110_16610 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___110_16610.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___110_16610.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___110_16610.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___110_16610.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___110_16610.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___110_16610.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___110_16610.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___110_16610.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___110_16610.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___110_16610.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___110_16610.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___110_16610.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___110_16610.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___110_16610.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___110_16610.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___110_16610.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___110_16610.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___110_16610.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___110_16610.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___110_16610.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___110_16610.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___110_16610.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___110_16610.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___110_16610.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___110_16610.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___110_16610.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___110_16610.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___110_16610.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___110_16610.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___110_16610.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___110_16610.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___110_16610.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___110_16610.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___110_16610.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___110_16610.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___110_16610.FStar_TypeChecker_Env.dep_graph)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____16614 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____16614
                       | uu____16615 ->
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
      let uu____16628 =
        let uu____16629 = FStar_Syntax_Subst.compress e  in
        uu____16629.FStar_Syntax_Syntax.n  in
      match uu____16628 with
      | FStar_Syntax_Syntax.Tm_bvar uu____16634 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____16639 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____16666 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____16682) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____16705,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____16732) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____16739 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____16739 with | ((uu____16750,t),uu____16752) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____16758 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____16758
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16759,(FStar_Util.Inl t,uu____16761),uu____16762) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16809,(FStar_Util.Inr c,uu____16811),uu____16812) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____16860 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____16869;
             FStar_Syntax_Syntax.vars = uu____16870;_},us)
          ->
          let uu____16876 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____16876 with
           | ((us',t),uu____16889) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____16895 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____16895)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____16911 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____16912 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____16922) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____16945 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____16945 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____16965  ->
                      match uu____16965 with
                      | (b,uu____16971) ->
                          let uu____16972 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____16972) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____16977 = universe_of_aux env res  in
                 level_of_type env res uu____16977  in
               let u_c =
                 let uu____16979 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res  in
                 match uu____16979 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____16983 = universe_of_aux env trepr  in
                     level_of_type env trepr uu____16983
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
            | FStar_Syntax_Syntax.Tm_bvar uu____17082 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____17097 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____17136 ->
                let uu____17137 = universe_of_aux env hd3  in
                (uu____17137, args1)
            | FStar_Syntax_Syntax.Tm_name uu____17150 ->
                let uu____17151 = universe_of_aux env hd3  in
                (uu____17151, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____17164 ->
                let uu____17181 = universe_of_aux env hd3  in
                (uu____17181, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____17194 ->
                let uu____17201 = universe_of_aux env hd3  in
                (uu____17201, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____17214 ->
                let uu____17241 = universe_of_aux env hd3  in
                (uu____17241, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____17254 ->
                let uu____17261 = universe_of_aux env hd3  in
                (uu____17261, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____17274 ->
                let uu____17275 = universe_of_aux env hd3  in
                (uu____17275, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____17288 ->
                let uu____17301 = universe_of_aux env hd3  in
                (uu____17301, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____17314 ->
                let uu____17321 = universe_of_aux env hd3  in
                (uu____17321, args1)
            | FStar_Syntax_Syntax.Tm_type uu____17334 ->
                let uu____17335 = universe_of_aux env hd3  in
                (uu____17335, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____17348,hd4::uu____17350) ->
                let uu____17415 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____17415 with
                 | (uu____17430,uu____17431,hd5) ->
                     let uu____17449 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____17449 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____17500 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env e
                   in
                let uu____17502 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____17502 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____17553 ->
                let uu____17554 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____17554 with
                 | (env1,uu____17576) ->
                     let env2 =
                       let uu___111_17582 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___111_17582.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___111_17582.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___111_17582.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___111_17582.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___111_17582.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___111_17582.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___111_17582.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___111_17582.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___111_17582.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___111_17582.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___111_17582.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___111_17582.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___111_17582.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___111_17582.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___111_17582.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___111_17582.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___111_17582.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___111_17582.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___111_17582.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___111_17582.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___111_17582.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___111_17582.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___111_17582.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___111_17582.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___111_17582.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___111_17582.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___111_17582.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___111_17582.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___111_17582.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___111_17582.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___111_17582.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___111_17582.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___111_17582.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___111_17582.FStar_TypeChecker_Env.dep_graph)
                       }  in
                     ((let uu____17584 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____17584
                       then
                         let uu____17585 =
                           let uu____17586 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____17586  in
                         let uu____17587 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____17585 uu____17587
                       else ());
                      (let uu____17589 = tc_term env2 hd3  in
                       match uu____17589 with
                       | (uu____17610,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____17611;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____17613;
                                        FStar_Syntax_Syntax.comp_thunk =
                                          uu____17614;_},g)
                           ->
                           ((let uu____17634 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____17634
                               (fun a240  -> ()));
                            (t, args1)))))
             in
          let uu____17645 = type_of_head true hd1 args  in
          (match uu____17645 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t
                  in
               let uu____17685 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____17685 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____17729 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____17729)))
      | FStar_Syntax_Syntax.Tm_match (uu____17732,hd1::uu____17734) ->
          let uu____17799 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____17799 with
           | (uu____17802,uu____17803,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____17821,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____17868 = universe_of_aux env e  in
      level_of_type env e uu____17868
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tps  ->
      let uu____17891 = tc_binders env tps  in
      match uu____17891 with
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
      let uu____17945 =
        let uu____17946 = FStar_Syntax_Subst.compress t  in
        uu____17946.FStar_Syntax_Syntax.n  in
      match uu____17945 with
      | FStar_Syntax_Syntax.Tm_delayed uu____17951 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____17978 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____17985 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____17985
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____17987 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____17987
            (fun uu____18001  ->
               match uu____18001 with
               | (t1,uu____18009) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____18011;
             FStar_Syntax_Syntax.vars = uu____18012;_},us)
          ->
          let uu____18018 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____18018
            (fun uu____18032  ->
               match uu____18032 with
               | (t1,uu____18040) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____18042 = tc_constant env t.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____18042
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____18044 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____18044
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____18053;_})
          ->
          let mk_comp =
            let uu____18089 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____18089
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____18109 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____18109
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____18156 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____18156
                 (fun u  ->
                    let uu____18164 =
                      let uu____18167 =
                        let uu____18174 =
                          let uu____18175 =
                            let uu____18188 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____18188)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____18175  in
                        FStar_Syntax_Syntax.mk uu____18174  in
                      uu____18167 FStar_Pervasives_Native.None
                        t.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____18164))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____18218 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____18218 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____18271 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____18271
                       (fun uc  ->
                          let uu____18279 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____18279)
                 | (x,imp)::bs3 ->
                     let uu____18297 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____18297
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____18306 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____18324) ->
          let uu____18329 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____18329
            (fun u_x  ->
               let uu____18337 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____18337)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____18375 =
              let uu____18376 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____18376.FStar_Syntax_Syntax.n  in
            match uu____18375 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____18438 = FStar_Util.first_N n_args bs  in
                    match uu____18438 with
                    | (bs1,rest) ->
                        let t1 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____18508 =
                          let uu____18513 = FStar_Syntax_Syntax.mk_Total t1
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____18513  in
                        (match uu____18508 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____18549 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____18549 with
                       | (bs1,c1) ->
                           let uu____18564 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____18564
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____18606  ->
                     match uu____18606 with
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
                         let uu____18652 = FStar_Syntax_Subst.subst subst1 t1
                            in
                         FStar_Pervasives_Native.Some uu____18652)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____18654) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____18660,uu____18661) ->
                aux t1
            | uu____18702 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____18703,(FStar_Util.Inl t1,uu____18705),uu____18706) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____18755,(FStar_Util.Inr c,uu____18757),uu____18758) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (uu____18807,t1) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____18842) ->
          type_of_well_typed_term env t1
      | FStar_Syntax_Syntax.Tm_match uu____18847 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____18870 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____18883 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____18894 = type_of_well_typed_term env t  in
      match uu____18894 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____18900;
            FStar_Syntax_Syntax.vars = uu____18901;_}
          -> FStar_Pervasives_Native.Some u
      | uu____18906 -> FStar_Pervasives_Native.None

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
            let uu___112_18931 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___112_18931.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___112_18931.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___112_18931.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___112_18931.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___112_18931.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___112_18931.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___112_18931.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___112_18931.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___112_18931.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___112_18931.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___112_18931.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___112_18931.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___112_18931.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___112_18931.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___112_18931.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___112_18931.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___112_18931.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___112_18931.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___112_18931.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___112_18931.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___112_18931.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___112_18931.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___112_18931.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___112_18931.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___112_18931.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___112_18931.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___112_18931.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___112_18931.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___112_18931.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___112_18931.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___112_18931.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___112_18931.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___112_18931.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___112_18931.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___112_18931.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___112_18931.FStar_TypeChecker_Env.dep_graph)
            }  in
          let slow_check uu____18937 =
            if must_total
            then
              let uu____18938 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____18938 with | (uu____18945,uu____18946,g) -> g
            else
              (let uu____18949 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____18949 with | (uu____18956,uu____18957,g) -> g)
             in
          let uu____18959 =
            let uu____18960 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____18960  in
          if uu____18959
          then slow_check ()
          else
            (let uu____18962 = type_of_well_typed_term env2 t  in
             match uu____18962 with
             | FStar_Pervasives_Native.None  -> slow_check ()
             | FStar_Pervasives_Native.Some k' ->
                 ((let uu____18967 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                       (FStar_Options.Other "FastImplicits")
                      in
                   if uu____18967
                   then
                     let uu____18968 =
                       FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                        in
                     let uu____18969 = FStar_Syntax_Print.term_to_string t
                        in
                     let uu____18970 = FStar_Syntax_Print.term_to_string k'
                        in
                     let uu____18971 = FStar_Syntax_Print.term_to_string k
                        in
                     FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                       uu____18968 uu____18969 uu____18970 uu____18971
                   else ());
                  (let b = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                   (let uu____18975 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                        (FStar_Options.Other "FastImplicits")
                       in
                    if uu____18975
                    then
                      let uu____18976 =
                        FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                         in
                      let uu____18977 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____18978 = FStar_Syntax_Print.term_to_string k'
                         in
                      let uu____18979 = FStar_Syntax_Print.term_to_string k
                         in
                      FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                        uu____18976 (if b then "succeeded" else "failed")
                        uu____18977 uu____18978 uu____18979
                    else ());
                   if b
                   then FStar_TypeChecker_Rel.trivial_guard
                   else slow_check ())))
  