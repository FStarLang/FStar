open Prims
let (instantiate_both :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___66_4 = env  in
    {
      FStar_TypeChecker_Env.solver = (uu___66_4.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___66_4.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___66_4.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___66_4.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___66_4.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___66_4.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___66_4.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___66_4.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___66_4.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___66_4.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___66_4.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___66_4.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___66_4.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___66_4.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___66_4.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___66_4.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___66_4.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___66_4.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___66_4.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___66_4.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___66_4.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___66_4.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___66_4.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___66_4.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___66_4.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___66_4.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___66_4.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___66_4.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___66_4.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.splice = (uu___66_4.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___66_4.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___66_4.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___66_4.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___66_4.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___66_4.FStar_TypeChecker_Env.dep_graph)
    }
  
let (no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___67_8 = env  in
    {
      FStar_TypeChecker_Env.solver = (uu___67_8.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___67_8.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___67_8.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___67_8.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___67_8.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___67_8.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___67_8.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___67_8.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___67_8.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___67_8.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___67_8.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___67_8.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___67_8.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___67_8.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___67_8.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___67_8.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___67_8.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___67_8.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___67_8.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___67_8.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___67_8.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___67_8.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___67_8.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___67_8.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___67_8.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___67_8.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___67_8.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___67_8.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___67_8.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.splice = (uu___67_8.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___67_8.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___67_8.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___67_8.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___67_8.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___67_8.FStar_TypeChecker_Env.dep_graph)
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
           let uu____40 =
             let uu____41 =
               let uu____42 = FStar_Syntax_Syntax.as_arg v1  in
               let uu____43 =
                 let uu____46 = FStar_Syntax_Syntax.as_arg tl1  in [uu____46]
                  in
               uu____42 :: uu____43  in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____41
              in
           uu____40 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
  
let (is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___61_53  ->
    match uu___61_53 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____56 -> false
  
let steps :
  'Auu____61 . 'Auu____61 -> FStar_TypeChecker_Normalize.step Prims.list =
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
            | uu____107 ->
                let t1 = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t1  in
                let uu____115 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____115 with
                 | FStar_Pervasives_Native.None  -> t1
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____125 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____127 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____127
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____129 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____130 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____129 uu____130
                             in
                          let uu____131 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____131
                           in
                        let s =
                          let uu____133 =
                            let uu____134 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____134
                             in
                          FStar_TypeChecker_Util.new_uvar env uu____133  in
                        let uu____143 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s  in
                        match uu____143 with
                        | FStar_Pervasives_Native.Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____148 -> fail ()))
             in
          aux false kt
  
let push_binding :
  'Auu____154 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____154) FStar_Pervasives_Native.tuple2 ->
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
        let uu____184 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____184
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
        (fun uu____196  ->
           let uu____197 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Util.set_result_typ uu____197 t)
  
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
                let uu____240 = FStar_Syntax_Syntax.mk_Total t  in
                FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____240
            | FStar_Util.Inr lc -> lc  in
          let t = lc.FStar_Syntax_Syntax.res_typ  in
          let uu____249 =
            let uu____256 = FStar_TypeChecker_Env.expected_typ env  in
            match uu____256 with
            | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                let uu____266 =
                  FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                    t'
                   in
                (match uu____266 with
                 | (e1,lc1) ->
                     let t1 = lc1.FStar_Syntax_Syntax.res_typ  in
                     let uu____282 =
                       FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t'
                        in
                     (match uu____282 with
                      | (e2,g) ->
                          ((let uu____296 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____296
                            then
                              let uu____297 =
                                FStar_Syntax_Print.term_to_string t1  in
                              let uu____298 =
                                FStar_Syntax_Print.term_to_string t'  in
                              let uu____299 =
                                FStar_TypeChecker_Rel.guard_to_string env g
                                 in
                              let uu____300 =
                                FStar_TypeChecker_Rel.guard_to_string env
                                  guard
                                 in
                              FStar_Util.print4
                                "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                uu____297 uu____298 uu____299 uu____300
                            else ());
                           (let msg =
                              let uu____307 =
                                FStar_TypeChecker_Rel.is_trivial g  in
                              if uu____307
                              then FStar_Pervasives_Native.None
                              else
                                FStar_All.pipe_left
                                  (fun _0_40  ->
                                     FStar_Pervasives_Native.Some _0_40)
                                  (FStar_TypeChecker_Err.subtyping_failed env
                                     t1 t')
                               in
                            let g1 = FStar_TypeChecker_Rel.conj_guard g guard
                               in
                            let uu____324 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                msg env e2 lc1 g1
                               in
                            match uu____324 with
                            | (lc2,g2) ->
                                let uu____337 = set_lcomp_result lc2 t'  in
                                ((memo_tk e2 t'), uu____337, g2)))))
             in
          match uu____249 with | (e1,lc1,g) -> (e1, lc1, g)
  
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
        let uu____368 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____368 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____378 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____378 with
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
        let uu____424 = ec  in
        match uu____424 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____445 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____445
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____447 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____447
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
            let uu____449 =
              match copt with
              | FStar_Pervasives_Native.Some uu____462 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____465 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____467 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____467))
                     in
                  if uu____465
                  then
                    let uu____474 =
                      let uu____477 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____477  in
                    (uu____474, c)
                  else
                    (let uu____481 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____481
                     then
                       let uu____488 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____488)
                     else
                       (let uu____492 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____492
                        then
                          let uu____499 =
                            let uu____502 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____502  in
                          (uu____499, c)
                        else (FStar_Pervasives_Native.None, c)))
               in
            (match uu____449 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1  in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let c3 =
                        let uu____529 = FStar_Syntax_Util.lcomp_of_comp c2
                           in
                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                          env e uu____529
                         in
                      let c4 = FStar_Syntax_Syntax.lcomp_comp c3  in
                      let uu____531 =
                        FStar_TypeChecker_Util.check_comp env e c4 expected_c
                         in
                      (match uu____531 with
                       | (e1,uu____545,g) ->
                           let g1 =
                             let uu____548 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_TypeChecker_Util.label_guard uu____548
                               "could not prove post-condition" g
                              in
                           ((let uu____550 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low
                                in
                             if uu____550
                             then
                               let uu____551 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos
                                  in
                               let uu____552 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1
                                  in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____551 uu____552
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
  'Auu____559 'Auu____560 .
    FStar_TypeChecker_Env.env ->
      ('Auu____559,'Auu____560,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____559,'Auu____560,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____580  ->
      match uu____580 with
      | (te,kt,f) ->
          let uu____590 = FStar_TypeChecker_Rel.guard_form f  in
          (match uu____590 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____598 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____603 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____598 uu____603)
  
let (print_expected_ty : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun env  ->
    let uu____613 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____613 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____617 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____617
  
let rec (get_pat_vars :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun pats  ->
    fun acc  ->
      let pats1 = FStar_Syntax_Util.unmeta pats  in
      let uu____641 = FStar_Syntax_Util.head_and_args pats1  in
      match uu____641 with
      | (head1,args) ->
          let uu____680 =
            let uu____681 = FStar_Syntax_Util.un_uinst head1  in
            uu____681.FStar_Syntax_Syntax.n  in
          (match uu____680 with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid
               ->
               let uu____688 = FStar_List.tl args  in
               get_pat_vars_args uu____688 acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.smtpatOr_lid
               -> get_pat_vars_args args acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               -> get_pat_vars_args args acc
           | uu____697 ->
               let uu____698 = FStar_Syntax_Free.names pats1  in
               FStar_Util.set_union acc uu____698)

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
  'Auu____728 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,'Auu____728) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____761 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____761
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____762;
                  FStar_Syntax_Syntax.effect_name = uu____763;
                  FStar_Syntax_Syntax.result_typ = uu____764;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____768)::[];
                  FStar_Syntax_Syntax.flags = uu____769;_}
                ->
                let pat_vars =
                  let uu____817 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta] env pats
                     in
                  let uu____818 =
                    FStar_Util.new_set FStar_Syntax_Syntax.order_bv  in
                  get_pat_vars uu____817 uu____818  in
                let uu____821 =
                  FStar_All.pipe_right bs
                    (FStar_Util.find_opt
                       (fun uu____848  ->
                          match uu____848 with
                          | (b,uu____854) ->
                              let uu____855 = FStar_Util.set_mem b pat_vars
                                 in
                              Prims.op_Negation uu____855))
                   in
                (match uu____821 with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some (x,uu____861) ->
                     let uu____866 =
                       let uu____871 =
                         let uu____872 = FStar_Syntax_Print.bv_to_string x
                            in
                         FStar_Util.format1
                           "Pattern misses at least one bound variable: %s"
                           uu____872
                          in
                       (FStar_Errors.Warning_PatternMissingBoundVar,
                         uu____871)
                        in
                     FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       uu____866)
            | uu____873 -> failwith "Impossible"
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
              let uu___68_923 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___68_923.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___68_923.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___68_923.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___68_923.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___68_923.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___68_923.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___68_923.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___68_923.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___68_923.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___68_923.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___68_923.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___68_923.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___68_923.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___68_923.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___68_923.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___68_923.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___68_923.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___68_923.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___68_923.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.failhard =
                  (uu___68_923.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___68_923.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.tc_term =
                  (uu___68_923.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___68_923.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___68_923.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___68_923.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___68_923.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___68_923.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___68_923.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth =
                  (uu___68_923.FStar_TypeChecker_Env.synth);
                FStar_TypeChecker_Env.splice =
                  (uu___68_923.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___68_923.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___68_923.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___68_923.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___68_923.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___68_923.FStar_TypeChecker_Env.dep_graph)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              (let uu____939 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
               if uu____939
               then
                 let uu____940 = FStar_Syntax_Print.binders_to_string ", " bs
                    in
                 let uu____941 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n" uu____940
                   uu____941
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____960  ->
                         match uu____960 with
                         | (b,uu____968) ->
                             let t =
                               let uu____970 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort
                                  in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____970
                                in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____973 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____974 -> []
                              | uu____987 ->
                                  let uu____988 =
                                    FStar_Syntax_Syntax.bv_to_name b  in
                                  [uu____988])))
                  in
               let as_lex_list dec =
                 let uu____993 = FStar_Syntax_Util.head_and_args dec  in
                 match uu____993 with
                 | (head1,uu____1009) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____1031 -> mk_lex_list [dec])
                  in
               let cflags = FStar_Syntax_Util.comp_flags c  in
               let uu____1035 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___62_1044  ->
                         match uu___62_1044 with
                         | FStar_Syntax_Syntax.DECREASES uu____1045 -> true
                         | uu____1048 -> false))
                  in
               match uu____1035 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____1052 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions  in
                   (match xs with | x::[] -> x | uu____1061 -> mk_lex_list xs))
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____1082 =
              match uu____1082 with
              | (l,t,u_names) ->
                  let uu____1100 =
                    let uu____1101 = FStar_Syntax_Subst.compress t  in
                    uu____1101.FStar_Syntax_Syntax.n  in
                  (match uu____1100 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____1162  ->
                                 match uu____1162 with
                                 | (x,imp) ->
                                     let uu____1173 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____1173
                                     then
                                       let uu____1178 =
                                         let uu____1179 =
                                           let uu____1182 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____1182
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____1179
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____1178, imp)
                                     else (x, imp)))
                          in
                       let uu____1184 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____1184 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____1203 =
                                let uu____1204 =
                                  let uu____1205 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____1206 =
                                    let uu____1209 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____1209]  in
                                  uu____1205 :: uu____1206  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____1204
                                 in
                              uu____1203 FStar_Pervasives_Native.None r  in
                            let uu____1212 = FStar_Util.prefix formals2  in
                            (match uu____1212 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___69_1259 = last1  in
                                   let uu____1260 =
                                     FStar_Syntax_Util.refine last1 precedes1
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___69_1259.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___69_1259.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____1260
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 ((let uu____1286 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low
                                      in
                                   if uu____1286
                                   then
                                     let uu____1287 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____1288 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____1289 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____1287 uu____1288 uu____1289
                                   else ());
                                  (l, t', u_names))))
                   | uu____1293 ->
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
        (let uu___70_1744 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___70_1744.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___70_1744.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___70_1744.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___70_1744.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___70_1744.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___70_1744.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___70_1744.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___70_1744.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___70_1744.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___70_1744.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___70_1744.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___70_1744.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___70_1744.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___70_1744.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___70_1744.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___70_1744.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___70_1744.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___70_1744.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___70_1744.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___70_1744.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___70_1744.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___70_1744.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___70_1744.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___70_1744.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___70_1744.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___70_1744.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___70_1744.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___70_1744.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___70_1744.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.splice =
             (uu___70_1744.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___70_1744.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___70_1744.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___70_1744.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___70_1744.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___70_1744.FStar_TypeChecker_Env.dep_graph)
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
      (let uu____1756 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____1756
       then
         let uu____1757 =
           let uu____1758 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1758  in
         let uu____1759 = FStar_Syntax_Print.tag_of_term e  in
         FStar_Util.print2 "%s (%s)\n" uu____1757 uu____1759
       else ());
      (let top = FStar_Syntax_Subst.compress e  in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1768 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1799 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1806 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1823 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1824 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1825 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1826 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1827 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1844 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1857 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1864 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = uu____1865;
              FStar_Syntax_Syntax.pos = uu____1866;
              FStar_Syntax_Syntax.vars = uu____1867;_},FStar_Syntax_Syntax.Meta_quoted
            (uu____1868,{ FStar_Syntax_Syntax.qopen = false ;_}))
           ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl FStar_Syntax_Syntax.t_term)
             FStar_TypeChecker_Rel.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = uu____1877;
              FStar_Syntax_Syntax.pos = uu____1878;
              FStar_Syntax_Syntax.vars = uu____1879;_},FStar_Syntax_Syntax.Meta_quoted
            (uu____1880,{ FStar_Syntax_Syntax.qopen = true ;_}))
           ->
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
           let uu____1896 =
             let uu____1903 =
               let uu____1908 = FStar_Syntax_Util.lcomp_of_comp c  in
               FStar_Util.Inr uu____1908  in
             value_check_expected_typ env1 top uu____1903
               FStar_TypeChecker_Rel.trivial_guard
              in
           (match uu____1896 with
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
           let uu____1931 = tc_tot_or_gtot_term env1 e1  in
           (match uu____1931 with
            | (e2,c,g) ->
                let g1 =
                  let uu___71_1948 = g  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___71_1948.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___71_1948.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___71_1948.FStar_TypeChecker_Env.implicits)
                  }  in
                let uu____1949 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____1949, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1970 = FStar_Syntax_Util.type_u ()  in
           (match uu____1970 with
            | (t,u) ->
                let uu____1983 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____1983 with
                 | (e2,c,g) ->
                     let uu____1999 =
                       let uu____2014 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____2014 with
                       | (env2,uu____2036) -> tc_pats env2 pats  in
                     (match uu____1999 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___72_2070 = g'  in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___72_2070.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___72_2070.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___72_2070.FStar_TypeChecker_Env.implicits)
                            }  in
                          let uu____2071 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____2074 =
                            FStar_TypeChecker_Rel.conj_guard g g'1  in
                          (uu____2071, c, uu____2074))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____2082 =
             let uu____2083 = FStar_Syntax_Subst.compress e1  in
             uu____2083.FStar_Syntax_Syntax.n  in
           (match uu____2082 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____2092,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____2094;
                               FStar_Syntax_Syntax.lbtyp = uu____2095;
                               FStar_Syntax_Syntax.lbeff = uu____2096;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____2098;
                               FStar_Syntax_Syntax.lbpos = uu____2099;_}::[]),e2)
                ->
                let uu____2127 =
                  let uu____2134 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____2134 e11  in
                (match uu____2127 with
                 | (e12,c1,g1) ->
                     let uu____2144 = tc_term env1 e2  in
                     (match uu____2144 with
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
                            let uu____2168 =
                              let uu____2171 =
                                let uu____2172 =
                                  let uu____2185 =
                                    let uu____2192 =
                                      let uu____2195 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____2195]  in
                                    (false, uu____2192)  in
                                  (uu____2185, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____2172  in
                              FStar_Syntax_Syntax.mk uu____2171  in
                            uu____2168 FStar_Pervasives_Native.None
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
                          let uu____2217 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2  in
                          (e5, c, uu____2217)))
            | uu____2220 ->
                let uu____2221 = tc_term env1 e1  in
                (match uu____2221 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2243) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____2255) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____2274 = tc_term env1 e1  in
           (match uu____2274 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____2298) ->
           let uu____2345 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____2345 with
            | (env0,uu____2359) ->
                let uu____2364 = tc_comp env0 expected_c  in
                (match uu____2364 with
                 | (expected_c1,uu____2378,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1
                        in
                     let uu____2383 =
                       let uu____2390 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res
                          in
                       tc_term uu____2390 e1  in
                     (match uu____2383 with
                      | (e2,c',g') ->
                          let uu____2400 =
                            let uu____2407 =
                              let uu____2412 =
                                FStar_Syntax_Syntax.lcomp_comp c'  in
                              (e2, uu____2412)  in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____2407
                             in
                          (match uu____2400 with
                           | (e3,expected_c2,g'') ->
                               let e4 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_ascribed
                                      (e3,
                                        ((FStar_Util.Inr expected_c2),
                                          FStar_Pervasives_Native.None),
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
                                 let uu____2457 =
                                   FStar_TypeChecker_Rel.conj_guard g' g''
                                    in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____2457
                                  in
                               let topt1 = tc_tactic_opt env0 topt  in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____2466 =
                                            FStar_Syntax_Util.mk_squash
                                              FStar_Syntax_Syntax.U_zero f1
                                             in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____2466)
                                  in
                               let uu____2467 =
                                 comp_check_expected_typ env1 e4 lc  in
                               (match uu____2467 with
                                | (e5,c,f2) ->
                                    let final_guard =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2
                                       in
                                    (e5, c, final_guard))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____2487) ->
           let uu____2534 = FStar_Syntax_Util.type_u ()  in
           (match uu____2534 with
            | (k,u) ->
                let uu____2547 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____2547 with
                 | (t1,uu____2561,f) ->
                     let uu____2563 =
                       let uu____2570 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                       tc_term uu____2570 e1  in
                     (match uu____2563 with
                      | (e2,c,g) ->
                          let uu____2580 =
                            let uu____2585 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos
                               in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____2589  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____2585 e2 c f
                             in
                          (match uu____2580 with
                           | (c1,f1) ->
                               let uu____2598 =
                                 let uu____2605 =
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
                                 comp_check_expected_typ env1 uu____2605 c1
                                  in
                               (match uu____2598 with
                                | (e3,c2,f2) ->
                                    let uu____2645 =
                                      let uu____2646 =
                                        FStar_TypeChecker_Rel.conj_guard g f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____2646
                                       in
                                    (e3, c2, uu____2645))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____2647;
              FStar_Syntax_Syntax.vars = uu____2648;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____2711 = FStar_Syntax_Util.head_and_args top  in
           (match uu____2711 with
            | (unary_op,uu____2733) ->
                let head1 =
                  let uu____2757 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2757
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
              FStar_Syntax_Syntax.pos = uu____2795;
              FStar_Syntax_Syntax.vars = uu____2796;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____2859 = FStar_Syntax_Util.head_and_args top  in
           (match uu____2859 with
            | (unary_op,uu____2881) ->
                let head1 =
                  let uu____2905 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2905
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
                (FStar_Const.Const_reflect uu____2943);
              FStar_Syntax_Syntax.pos = uu____2944;
              FStar_Syntax_Syntax.vars = uu____2945;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3008 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3008 with
            | (unary_op,uu____3030) ->
                let head1 =
                  let uu____3054 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3054
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
              FStar_Syntax_Syntax.pos = uu____3092;
              FStar_Syntax_Syntax.vars = uu____3093;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____3169 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3169 with
            | (unary_op,uu____3191) ->
                let head1 =
                  let uu____3215 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____3215
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
              FStar_Syntax_Syntax.pos = uu____3259;
              FStar_Syntax_Syntax.vars = uu____3260;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____3298 =
             let uu____3305 =
               let uu____3306 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3306  in
             tc_term uu____3305 e1  in
           (match uu____3298 with
            | (e2,c,g) ->
                let uu____3330 = FStar_Syntax_Util.head_and_args top  in
                (match uu____3330 with
                 | (head1,uu____3352) ->
                     let uu____3373 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____3400 =
                       let uu____3401 =
                         let uu____3404 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____3404  in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____3401
                        in
                     (uu____3373, uu____3400, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3409;
              FStar_Syntax_Syntax.vars = uu____3410;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____3463 = FStar_Syntax_Util.head_and_args top  in
           (match uu____3463 with
            | (head1,uu____3485) ->
                let env' =
                  let uu____3507 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____3507  in
                let uu____3508 = tc_term env' r  in
                (match uu____3508 with
                 | (er,uu____3522,gr) ->
                     let uu____3524 = tc_term env1 t  in
                     (match uu____3524 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Rel.conj_guard gr gt1  in
                          let uu____3541 =
                            let uu____3544 =
                              let uu____3545 =
                                let uu____3546 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____3547 =
                                  let uu____3550 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____3550]  in
                                uu____3546 :: uu____3547  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____3545
                               in
                            uu____3544 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____3541, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3555;
              FStar_Syntax_Syntax.vars = uu____3556;_},uu____3557)
           ->
           let uu____3578 =
             let uu____3583 =
               let uu____3584 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____3584  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____3583)  in
           FStar_Errors.raise_error uu____3578 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3591;
              FStar_Syntax_Syntax.vars = uu____3592;_},uu____3593)
           ->
           let uu____3614 =
             let uu____3619 =
               let uu____3620 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____3620  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____3619)  in
           FStar_Errors.raise_error uu____3614 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____3627;
              FStar_Syntax_Syntax.vars = uu____3628;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____3661 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____3661 with
             | (env0,uu____3675) ->
                 let uu____3680 = tc_term env0 e1  in
                 (match uu____3680 with
                  | (e2,c,g) ->
                      let uu____3696 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____3696 with
                       | (reify_op,uu____3718) ->
                           let u_c =
                             let uu____3740 =
                               tc_term env0 c.FStar_Syntax_Syntax.res_typ  in
                             match uu____3740 with
                             | (uu____3747,c',uu____3749) ->
                                 let uu____3750 =
                                   let uu____3751 =
                                     FStar_Syntax_Subst.compress
                                       c'.FStar_Syntax_Syntax.res_typ
                                      in
                                   uu____3751.FStar_Syntax_Syntax.n  in
                                 (match uu____3750 with
                                  | FStar_Syntax_Syntax.Tm_type u -> u
                                  | uu____3755 ->
                                      let uu____3756 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____3756 with
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
                                                 let uu____3768 =
                                                   let uu____3769 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       c'
                                                      in
                                                   let uu____3770 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   let uu____3771 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c'.FStar_Syntax_Syntax.res_typ
                                                      in
                                                   FStar_Util.format3
                                                     "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                     uu____3769 uu____3770
                                                     uu____3771
                                                    in
                                                 failwith uu____3768);
                                            u)))
                              in
                           let repr =
                             let uu____3773 =
                               FStar_Syntax_Syntax.lcomp_comp c  in
                             FStar_TypeChecker_Env.reify_comp env1 uu____3773
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
                             let uu____3794 =
                               FStar_Syntax_Syntax.mk_Total repr  in
                             FStar_All.pipe_right uu____3794
                               FStar_Syntax_Util.lcomp_of_comp
                              in
                           let uu____3795 =
                             comp_check_expected_typ env1 e3 c1  in
                           (match uu____3795 with
                            | (e4,c2,g') ->
                                let uu____3811 =
                                  FStar_TypeChecker_Rel.conj_guard g g'  in
                                (e4, c2, uu____3811))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____3813;
              FStar_Syntax_Syntax.vars = uu____3814;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let no_reflect uu____3856 =
               let uu____3857 =
                 let uu____3862 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____3862)  in
               FStar_Errors.raise_error uu____3857 e1.FStar_Syntax_Syntax.pos
                in
             let uu____3869 = FStar_Syntax_Util.head_and_args top  in
             match uu____3869 with
             | (reflect_op,uu____3891) ->
                 let uu____3912 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____3912 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____3945 =
                        let uu____3946 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable
                           in
                        Prims.op_Negation uu____3946  in
                      if uu____3945
                      then no_reflect ()
                      else
                        (let uu____3956 =
                           FStar_TypeChecker_Env.clear_expected_typ env1  in
                         match uu____3956 with
                         | (env_no_ex,topt) ->
                             let uu____3975 =
                               let u = FStar_TypeChecker_Env.new_u_univ ()
                                  in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr))
                                  in
                               let t =
                                 let uu____3995 =
                                   let uu____3998 =
                                     let uu____3999 =
                                       let uu____4014 =
                                         let uu____4017 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         let uu____4018 =
                                           let uu____4021 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun
                                              in
                                           [uu____4021]  in
                                         uu____4017 :: uu____4018  in
                                       (repr, uu____4014)  in
                                     FStar_Syntax_Syntax.Tm_app uu____3999
                                      in
                                   FStar_Syntax_Syntax.mk uu____3998  in
                                 uu____3995 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos
                                  in
                               let uu____4027 =
                                 let uu____4034 =
                                   let uu____4035 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1
                                      in
                                   FStar_All.pipe_right uu____4035
                                     FStar_Pervasives_Native.fst
                                    in
                                 tc_tot_or_gtot_term uu____4034 t  in
                               match uu____4027 with
                               | (t1,uu____4063,g) ->
                                   let uu____4065 =
                                     let uu____4066 =
                                       FStar_Syntax_Subst.compress t1  in
                                     uu____4066.FStar_Syntax_Syntax.n  in
                                   (match uu____4065 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____4081,(res,uu____4083)::
                                         (wp,uu____4085)::[])
                                        -> (t1, res, wp, g)
                                    | uu____4128 -> failwith "Impossible")
                                in
                             (match uu____3975 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____4159 =
                                    let uu____4164 =
                                      tc_tot_or_gtot_term env_no_ex e1  in
                                    match uu____4164 with
                                    | (e2,c,g) ->
                                        ((let uu____4179 =
                                            let uu____4180 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c
                                               in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____4180
                                             in
                                          if uu____4179
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [(FStar_Errors.Error_UnexpectedGTotComputation,
                                                 "Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____4194 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ
                                             in
                                          match uu____4194 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____4202 =
                                                  let uu____4211 =
                                                    let uu____4218 =
                                                      let uu____4219 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr
                                                         in
                                                      let uu____4220 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____4219 uu____4220
                                                       in
                                                    (FStar_Errors.Error_UnexpectedInstance,
                                                      uu____4218,
                                                      (e2.FStar_Syntax_Syntax.pos))
                                                     in
                                                  [uu____4211]  in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____4202);
                                               (let uu____4233 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                (e2, uu____4233)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____4235 =
                                                let uu____4236 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0
                                                   in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____4236
                                                 in
                                              (e2, uu____4235)))
                                     in
                                  (match uu____4159 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____4246 =
                                           let uu____4247 =
                                             let uu____4248 =
                                               let uu____4249 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ
                                                  in
                                               [uu____4249]  in
                                             let uu____4250 =
                                               let uu____4259 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp
                                                  in
                                               [uu____4259]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____4248;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____4250;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____4247
                                            in
                                         FStar_All.pipe_right uu____4246
                                           FStar_Syntax_Util.lcomp_of_comp
                                          in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____4279 =
                                         comp_check_expected_typ env1 e3 c
                                          in
                                       (match uu____4279 with
                                        | (e4,c1,g') ->
                                            let uu____4295 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g
                                               in
                                            (e4, c1, uu____4295))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____4342 =
               let uu____4343 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____4343 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____4342 instantiate_both  in
           ((let uu____4359 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____4359
             then
               let uu____4360 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____4361 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____4360
                 uu____4361
             else ());
            (let uu____4363 = tc_term (no_inst env2) head1  in
             match uu____4363 with
             | (head2,chead,g_head) ->
                 let uu____4379 =
                   let uu____4386 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2)
                      in
                   if uu____4386
                   then
                     let uu____4393 =
                       let uu____4400 =
                         FStar_TypeChecker_Env.expected_typ env0  in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____4400
                        in
                     match uu____4393 with | (e1,c,g) -> (e1, c, g)
                   else
                     (let uu____4413 =
                        FStar_TypeChecker_Env.expected_typ env0  in
                      check_application_args env2 head2 chead g_head args
                        uu____4413)
                    in
                 (match uu____4379 with
                  | (e1,c,g) ->
                      ((let uu____4426 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme
                           in
                        if uu____4426
                        then
                          let uu____4427 =
                            FStar_TypeChecker_Rel.print_pending_implicits g
                             in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____4427
                        else ());
                       (let uu____4429 = comp_check_expected_typ env0 e1 c
                           in
                        match uu____4429 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____4446 =
                                let uu____4447 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____4447.FStar_Syntax_Syntax.n  in
                              match uu____4446 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____4451) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos))
                                     in
                                  let uu___73_4513 =
                                    FStar_TypeChecker_Rel.trivial_guard  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___73_4513.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___73_4513.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___73_4513.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____4562 ->
                                  FStar_TypeChecker_Rel.trivial_guard
                               in
                            let gres =
                              let uu____4564 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp  in
                              FStar_TypeChecker_Rel.conj_guard g uu____4564
                               in
                            ((let uu____4566 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme
                                 in
                              if uu____4566
                              then
                                let uu____4567 =
                                  FStar_Syntax_Print.term_to_string e2  in
                                let uu____4568 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres
                                   in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____4567 uu____4568
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____4608 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____4608 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____4628 = tc_term env12 e1  in
                (match uu____4628 with
                 | (e11,c1,g1) ->
                     let uu____4644 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____4654 = FStar_Syntax_Util.type_u ()  in
                           (match uu____4654 with
                            | (k,uu____4664) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k  in
                                let uu____4666 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t
                                   in
                                (uu____4666, res_t))
                        in
                     (match uu____4644 with
                      | (env_branches,res_t) ->
                          ((let uu____4676 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____4676
                            then
                              let uu____4677 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____4677
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
                            let uu____4787 =
                              let uu____4792 =
                                FStar_List.fold_right
                                  (fun uu____4864  ->
                                     fun uu____4865  ->
                                       match (uu____4864, uu____4865) with
                                       | ((branch1,f,eff_label,cflags,c,g),
                                          (caccum,gaccum)) ->
                                           let uu____5070 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum
                                              in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____5070)) t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard)
                                 in
                              match uu____4792 with
                              | (cases,g) ->
                                  let uu____5161 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____5161, g)
                               in
                            match uu____4787 with
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
                                           (fun uu____5275  ->
                                              match uu____5275 with
                                              | ((pat,wopt,br),uu____5311,eff_label,uu____5313,uu____5314,uu____5315)
                                                  ->
                                                  let uu____5336 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t
                                                     in
                                                  (pat, wopt, uu____5336)))
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
                                  let uu____5391 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name
                                     in
                                  if uu____5391
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____5398 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____5398  in
                                     let lb =
                                       let uu____5402 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name
                                          in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_Syntax_Syntax.res_typ
                                         uu____5402 e11 []
                                         e11.FStar_Syntax_Syntax.pos
                                        in
                                     let e2 =
                                       let uu____5408 =
                                         let uu____5411 =
                                           let uu____5412 =
                                             let uu____5425 =
                                               let uu____5426 =
                                                 let uu____5427 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____5427]  in
                                               FStar_Syntax_Subst.close
                                                 uu____5426 e_match
                                                in
                                             ((false, [lb]), uu____5425)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____5412
                                            in
                                         FStar_Syntax_Syntax.mk uu____5411
                                          in
                                       uu____5408
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ)
                                   in
                                ((let uu____5440 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____5440
                                  then
                                    let uu____5441 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____5442 =
                                      FStar_Syntax_Print.lcomp_to_string cres
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____5441 uu____5442
                                  else ());
                                 (let uu____5444 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches
                                     in
                                  (e2, cres, uu____5444))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5447;
                FStar_Syntax_Syntax.lbunivs = uu____5448;
                FStar_Syntax_Syntax.lbtyp = uu____5449;
                FStar_Syntax_Syntax.lbeff = uu____5450;
                FStar_Syntax_Syntax.lbdef = uu____5451;
                FStar_Syntax_Syntax.lbattrs = uu____5452;
                FStar_Syntax_Syntax.lbpos = uu____5453;_}::[]),uu____5454)
           ->
           ((let uu____5478 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____5478
             then
               let uu____5479 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" uu____5479
             else ());
            (let uu____5481 = FStar_Options.use_two_phase_tc ()  in
             if uu____5481
             then
               let is_lb_unannotated t =
                 match t.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_let
                     ((uu____5492,lb::[]),uu____5494) ->
                     let uu____5507 =
                       let uu____5508 =
                         FStar_Syntax_Subst.compress
                           lb.FStar_Syntax_Syntax.lbtyp
                          in
                       uu____5508.FStar_Syntax_Syntax.n  in
                     uu____5507 = FStar_Syntax_Syntax.Tm_unknown
                 | uu____5511 -> failwith "Impossible"  in
               let drop_lbtyp t =
                 match t.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_let ((t1,lb::[]),t2) ->
                     let uu___74_5531 = t  in
                     let uu____5532 =
                       let uu____5533 =
                         let uu____5546 =
                           let uu____5553 =
                             let uu____5556 =
                               let uu___75_5557 = lb  in
                               let uu____5558 =
                                 FStar_Syntax_Syntax.mk
                                   FStar_Syntax_Syntax.Tm_unknown
                                   FStar_Pervasives_Native.None
                                   (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.pos
                                  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___75_5557.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___75_5557.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = uu____5558;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___75_5557.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___75_5557.FStar_Syntax_Syntax.lbdef);
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___75_5557.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___75_5557.FStar_Syntax_Syntax.lbpos)
                               }  in
                             [uu____5556]  in
                           (t1, uu____5553)  in
                         (uu____5546, t2)  in
                       FStar_Syntax_Syntax.Tm_let uu____5533  in
                     {
                       FStar_Syntax_Syntax.n = uu____5532;
                       FStar_Syntax_Syntax.pos =
                         (uu___74_5531.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___74_5531.FStar_Syntax_Syntax.vars)
                     }
                 | uu____5571 -> failwith "Impossible"  in
               let uu____5572 =
                 check_top_level_let
                   (let uu___76_5581 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___76_5581.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___76_5581.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___76_5581.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___76_5581.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___76_5581.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___76_5581.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___76_5581.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___76_5581.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___76_5581.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___76_5581.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___76_5581.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___76_5581.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___76_5581.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___76_5581.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___76_5581.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___76_5581.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___76_5581.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___76_5581.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___76_5581.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___76_5581.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___76_5581.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___76_5581.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___76_5581.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___76_5581.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___76_5581.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___76_5581.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___76_5581.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___76_5581.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___76_5581.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.splice =
                        (uu___76_5581.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___76_5581.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___76_5581.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___76_5581.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___76_5581.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___76_5581.FStar_TypeChecker_Env.dep_graph)
                    }) top
                  in
               match uu____5572 with
               | (lax_top,l,g) ->
                   let lax_top1 =
                     FStar_TypeChecker_Normalize.remove_uvar_solutions env1
                       lax_top
                      in
                   ((let uu____5593 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____5593
                     then
                       let uu____5594 =
                         FStar_Syntax_Print.term_to_string lax_top1  in
                       FStar_Util.print1 "Phase 1: checked %s\n" uu____5594
                     else ());
                    (let uu____5596 =
                       FStar_TypeChecker_Env.should_verify env1  in
                     if uu____5596
                     then
                       let uu____5603 =
                         let uu____5604 = is_lb_unannotated top  in
                         if uu____5604 then drop_lbtyp lax_top1 else lax_top1
                          in
                       check_top_level_let env1 uu____5603
                     else (lax_top1, l, g)))
             else check_top_level_let env1 top))
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____5608),uu____5609) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5624;
                FStar_Syntax_Syntax.lbunivs = uu____5625;
                FStar_Syntax_Syntax.lbtyp = uu____5626;
                FStar_Syntax_Syntax.lbeff = uu____5627;
                FStar_Syntax_Syntax.lbdef = uu____5628;
                FStar_Syntax_Syntax.lbattrs = uu____5629;
                FStar_Syntax_Syntax.lbpos = uu____5630;_}::uu____5631),uu____5632)
           ->
           ((let uu____5658 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____5658
             then
               let uu____5659 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.print1 "%s\n" uu____5659
             else ());
            (let uu____5661 = FStar_Options.use_two_phase_tc ()  in
             if uu____5661
             then
               let uu____5668 =
                 check_top_level_let_rec
                   (let uu___77_5677 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___77_5677.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___77_5677.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___77_5677.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___77_5677.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___77_5677.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___77_5677.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___77_5677.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___77_5677.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___77_5677.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___77_5677.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___77_5677.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___77_5677.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___77_5677.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___77_5677.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___77_5677.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___77_5677.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___77_5677.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___77_5677.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___77_5677.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___77_5677.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___77_5677.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___77_5677.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___77_5677.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___77_5677.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___77_5677.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___77_5677.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___77_5677.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___77_5677.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___77_5677.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.splice =
                        (uu___77_5677.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___77_5677.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___77_5677.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___77_5677.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___77_5677.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___77_5677.FStar_TypeChecker_Env.dep_graph)
                    }) top
                  in
               match uu____5668 with
               | (lax_top,l,g) ->
                   let lax_top1 =
                     FStar_TypeChecker_Normalize.remove_uvar_solutions env1
                       lax_top
                      in
                   ((let uu____5689 =
                       FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____5689
                     then
                       let uu____5690 =
                         FStar_Syntax_Print.term_to_string lax_top1  in
                       FStar_Util.print1 "Phase 1: checked %s\n" uu____5690
                     else ());
                    (let uu____5692 =
                       FStar_TypeChecker_Env.should_verify env1  in
                     if uu____5692
                     then check_top_level_let_rec env1 lax_top1
                     else (lax_top1, l, g)))
             else check_top_level_let_rec env1 top))
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____5701),uu____5702) ->
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
        let uu____5728 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5818))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5878))::(uu____5879,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____5880))::
              (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____5953 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_SynthByTacticError,
                  "synth_by_tactic: bad application") rng
           in
        match uu____5728 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____6037 = FStar_TypeChecker_Env.expected_typ env  in
                  (match uu____6037 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____6043 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_SynthByTacticError,
                           "synth_by_tactic: need a type annotation when no expected type is present")
                         uu____6043)
               in
            let uu____6046 = FStar_TypeChecker_Env.clear_expected_typ env  in
            (match uu____6046 with
             | (env',uu____6060) ->
                 let uu____6065 = tc_term env' typ  in
                 (match uu____6065 with
                  | (typ1,uu____6079,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____6082 = tc_tactic env' tau  in
                        match uu____6082 with
                        | (tau1,uu____6096,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let t =
                                if env.FStar_TypeChecker_Env.nosynth
                                then
                                  let uu____6104 =
                                    let uu____6105 =
                                      FStar_TypeChecker_Util.fvar_const env
                                        FStar_Parser_Const.magic_lid
                                       in
                                    let uu____6106 =
                                      let uu____6107 =
                                        FStar_Syntax_Syntax.as_arg
                                          FStar_Syntax_Util.exp_unit
                                         in
                                      [uu____6107]  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6105
                                      uu____6106
                                     in
                                  uu____6104 FStar_Pervasives_Native.None rng
                                else
                                  (let t =
                                     env.FStar_TypeChecker_Env.synth env'
                                       typ1 tau1
                                      in
                                   (let uu____6113 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Tac")
                                       in
                                    if uu____6113
                                    then
                                      let uu____6114 =
                                        FStar_Syntax_Print.term_to_string t
                                         in
                                      FStar_Util.print1 "Got %s\n" uu____6114
                                    else ());
                                   t)
                                 in
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____6117 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng
                                  in
                               tc_term env uu____6117)))))))

and (tc_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___78_6121 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___78_6121.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___78_6121.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___78_6121.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___78_6121.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___78_6121.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___78_6121.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___78_6121.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___78_6121.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___78_6121.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___78_6121.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___78_6121.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___78_6121.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___78_6121.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___78_6121.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___78_6121.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___78_6121.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___78_6121.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___78_6121.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___78_6121.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___78_6121.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___78_6121.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___78_6121.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___78_6121.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___78_6121.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___78_6121.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___78_6121.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___78_6121.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___78_6121.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___78_6121.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.splice =
            (uu___78_6121.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___78_6121.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___78_6121.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___78_6121.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___78_6121.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___78_6121.FStar_TypeChecker_Env.dep_graph)
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
        let uu___79_6125 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___79_6125.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___79_6125.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___79_6125.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___79_6125.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___79_6125.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___79_6125.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___79_6125.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___79_6125.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___79_6125.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___79_6125.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___79_6125.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___79_6125.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___79_6125.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___79_6125.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___79_6125.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___79_6125.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___79_6125.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___79_6125.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___79_6125.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___79_6125.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___79_6125.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___79_6125.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___79_6125.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___79_6125.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___79_6125.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___79_6125.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___79_6125.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___79_6125.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___79_6125.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.splice =
            (uu___79_6125.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___79_6125.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___79_6125.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___79_6125.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___79_6125.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___79_6125.FStar_TypeChecker_Env.dep_graph)
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
          let uu____6141 = tc_tactic env tactic  in
          (match uu____6141 with
           | (tactic1,uu____6151,uu____6152) ->
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
        let uu____6191 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____6191 with
        | (e2,t,implicits) ->
            let tc =
              let uu____6212 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____6212
              then FStar_Util.Inl t
              else
                (let uu____6218 =
                   let uu____6219 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____6219
                    in
                 FStar_Util.Inr uu____6218)
               in
            let is_data_ctor uu___63_6229 =
              match uu___63_6229 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____6232) -> true
              | uu____6239 -> false  in
            let uu____6242 =
              (is_data_ctor dc) &&
                (let uu____6244 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____6244)
               in
            if uu____6242
            then
              let uu____6251 =
                let uu____6256 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____6256)  in
              let uu____6257 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____6251 uu____6257
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____6274 =
            let uu____6275 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____6275
             in
          failwith uu____6274
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____6309 =
              let uu____6310 = FStar_Syntax_Subst.compress t1  in
              uu____6310.FStar_Syntax_Syntax.n  in
            match uu____6309 with
            | FStar_Syntax_Syntax.Tm_arrow uu____6313 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____6326 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos))
                   in
                let uu___80_6364 = FStar_TypeChecker_Rel.trivial_guard  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___80_6364.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___80_6364.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___80_6364.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                }
             in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____6416 =
            let uu____6429 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____6429 with
            | FStar_Pervasives_Native.None  ->
                let uu____6444 = FStar_Syntax_Util.type_u ()  in
                (match uu____6444 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard)
             in
          (match uu____6416 with
           | (t,uu____6481,g0) ->
               let uu____6495 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____6495 with
                | (e1,uu____6515,g1) ->
                    let uu____6529 =
                      let uu____6530 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____6530
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    let uu____6531 = FStar_TypeChecker_Rel.conj_guard g0 g1
                       in
                    (e1, uu____6529, uu____6531)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____6533 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____6546 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____6546)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____6533 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___81_6565 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___81_6565.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___81_6565.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____6568 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____6568 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____6589 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____6589
                       then FStar_Util.Inl t1
                       else
                         (let uu____6595 =
                            let uu____6596 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____6596
                             in
                          FStar_Util.Inr uu____6595)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6602;
             FStar_Syntax_Syntax.vars = uu____6603;_},uu____6604)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____6609 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____6609
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____6617 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____6617
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6625;
             FStar_Syntax_Syntax.vars = uu____6626;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____6635 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6635 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____6658 =
                     let uu____6663 =
                       let uu____6664 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____6665 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____6666 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____6664 uu____6665 uu____6666
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____6663)
                      in
                   let uu____6667 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____6658 uu____6667)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____6683 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6687 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6687 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6689 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6689 with
           | ((us,t),range) ->
               ((let uu____6712 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____6712
                 then
                   let uu____6713 =
                     let uu____6714 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____6714  in
                   let uu____6715 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____6716 = FStar_Range.string_of_range range  in
                   let uu____6717 = FStar_Range.string_of_use_range range  in
                   let uu____6718 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____6713 uu____6715 uu____6716 uu____6717 uu____6718
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6723 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6723 us  in
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
          let uu____6747 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6747 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____6761 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____6761 with
                | (env2,uu____6775) ->
                    let uu____6780 = tc_binders env2 bs1  in
                    (match uu____6780 with
                     | (bs2,env3,g,us) ->
                         let uu____6799 = tc_comp env3 c1  in
                         (match uu____6799 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___82_6818 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___82_6818.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___82_6818.FStar_Syntax_Syntax.vars)
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
                                  let uu____6827 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____6827
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
          let uu____6846 =
            let uu____6851 =
              let uu____6852 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____6852]  in
            FStar_Syntax_Subst.open_term uu____6851 phi  in
          (match uu____6846 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____6862 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               (match uu____6862 with
                | (env2,uu____6876) ->
                    let uu____6881 =
                      let uu____6894 = FStar_List.hd x1  in
                      tc_binder env2 uu____6894  in
                    (match uu____6881 with
                     | (x2,env3,f1,u) ->
                         ((let uu____6922 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____6922
                           then
                             let uu____6923 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____6924 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____6925 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____6923 uu____6924 uu____6925
                           else ());
                          (let uu____6927 = FStar_Syntax_Util.type_u ()  in
                           match uu____6927 with
                           | (t_phi,uu____6939) ->
                               let uu____6940 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____6940 with
                                | (phi2,uu____6954,f2) ->
                                    let e1 =
                                      let uu___83_6959 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___83_6959.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___83_6959.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____6966 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____6966
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____6979) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____7002 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
            if uu____7002
            then
              let uu____7003 =
                FStar_Syntax_Print.term_to_string
                  (let uu___84_7006 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___84_7006.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___84_7006.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____7003
            else ());
           (let uu____7012 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____7012 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____7025 ->
          let uu____7026 =
            let uu____7027 = FStar_Syntax_Print.term_to_string top  in
            let uu____7028 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____7027
              uu____7028
             in
          failwith uu____7026

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____7038 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____7039,FStar_Pervasives_Native.None ) ->
            FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____7050,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____7066 -> FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_float uu____7071 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____7072 ->
            let uu____7073 =
              let uu____7078 =
                FStar_Syntax_DsEnv.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
                 in
              FStar_All.pipe_right uu____7078 FStar_Util.must  in
            FStar_All.pipe_right uu____7073 FStar_Pervasives_Native.fst
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____7103 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____7104 =
              let uu____7109 =
                let uu____7110 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7110
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7109)  in
            FStar_Errors.raise_error uu____7104 r
        | FStar_Const.Const_set_range_of  ->
            let uu____7111 =
              let uu____7116 =
                let uu____7117 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7117
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7116)  in
            FStar_Errors.raise_error uu____7111 r
        | FStar_Const.Const_reify  ->
            let uu____7118 =
              let uu____7123 =
                let uu____7124 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7124
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7123)  in
            FStar_Errors.raise_error uu____7118 r
        | FStar_Const.Const_reflect uu____7125 ->
            let uu____7126 =
              let uu____7131 =
                let uu____7132 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7132
                 in
              (FStar_Errors.Fatal_IllTyped, uu____7131)  in
            FStar_Errors.raise_error uu____7126 r
        | uu____7133 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____7150) ->
          let uu____7159 = FStar_Syntax_Util.type_u ()  in
          (match uu____7159 with
           | (k,u) ->
               let uu____7172 = tc_check_tot_or_gtot_term env t k  in
               (match uu____7172 with
                | (t1,uu____7186,g) ->
                    let uu____7188 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____7188, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____7190) ->
          let uu____7199 = FStar_Syntax_Util.type_u ()  in
          (match uu____7199 with
           | (k,u) ->
               let uu____7212 = tc_check_tot_or_gtot_term env t k  in
               (match uu____7212 with
                | (t1,uu____7226,g) ->
                    let uu____7228 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____7228, u, g)))
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
            let uu____7236 =
              let uu____7237 =
                let uu____7238 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____7238 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____7237  in
            uu____7236 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____7241 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____7241 with
           | (tc1,uu____7255,f) ->
               let uu____7257 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____7257 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____7301 =
                        let uu____7302 = FStar_Syntax_Subst.compress head3
                           in
                        uu____7302.FStar_Syntax_Syntax.n  in
                      match uu____7301 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____7305,us) -> us
                      | uu____7311 -> []  in
                    let uu____7312 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____7312 with
                     | (uu____7333,args1) ->
                         let uu____7355 =
                           let uu____7374 = FStar_List.hd args1  in
                           let uu____7387 = FStar_List.tl args1  in
                           (uu____7374, uu____7387)  in
                         (match uu____7355 with
                          | (res,args2) ->
                              let uu____7452 =
                                let uu____7461 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___64_7489  ->
                                          match uu___64_7489 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____7497 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____7497 with
                                               | (env1,uu____7509) ->
                                                   let uu____7514 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____7514 with
                                                    | (e1,uu____7526,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____7461
                                  FStar_List.unzip
                                 in
                              (match uu____7452 with
                               | (flags1,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___85_7565 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___85_7565.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___85_7565.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     let uu____7569 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u
                                        in
                                     match uu____7569 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm
                                      in
                                   let uu____7573 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____7573))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____7581 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____7582 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____7592 = aux u3  in FStar_Syntax_Syntax.U_succ uu____7592
        | FStar_Syntax_Syntax.U_max us ->
            let uu____7596 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____7596
        | FStar_Syntax_Syntax.U_name x -> u2  in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____7601 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____7601 FStar_Pervasives_Native.snd
         | uu____7610 -> aux u)

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
          let fail a msg t =
            let uu____7631 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____7631 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____7725 bs2 bs_expected1 =
              match uu____7725 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____7893)) ->
                             let uu____7898 =
                               let uu____7903 =
                                 let uu____7904 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____7904
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____7903)
                                in
                             let uu____7905 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____7898 uu____7905
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____7906),FStar_Pervasives_Native.None ) ->
                             let uu____7911 =
                               let uu____7916 =
                                 let uu____7917 =
                                   FStar_Syntax_Print.bv_to_string hd1  in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____7917
                                  in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____7916)
                                in
                             let uu____7918 =
                               FStar_Syntax_Syntax.range_of_bv hd1  in
                             FStar_Errors.raise_error uu____7911 uu____7918
                         | uu____7919 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____7925 =
                           let uu____7930 =
                             let uu____7931 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____7931.FStar_Syntax_Syntax.n  in
                           match uu____7930 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____7938 ->
                               ((let uu____7940 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____7940
                                 then
                                   let uu____7941 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____7941
                                 else ());
                                (let uu____7943 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____7943 with
                                 | (t,uu____7955,g1) ->
                                     let g2 =
                                       let uu____7958 =
                                         FStar_TypeChecker_Rel.teq_nosmt env2
                                           t expected_t
                                          in
                                       if uu____7958
                                       then
                                         FStar_TypeChecker_Rel.trivial_guard
                                       else
                                         (let uu____7960 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t
                                             in
                                          match uu____7960 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____7963 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t
                                                 in
                                              let uu____7968 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_Errors.raise_error
                                                uu____7963 uu____7968
                                          | FStar_Pervasives_Native.Some g2
                                              ->
                                              let uu____7970 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____7970
                                                "Type annotation on parameter incompatible with the expected type"
                                                g2)
                                        in
                                     let g3 =
                                       let uu____7972 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2
                                          in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____7972
                                        in
                                     (t, g3)))
                            in
                         match uu____7925 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___86_8000 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___86_8000.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___86_8000.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env3 = push_binding env2 b  in
                             let subst2 =
                               let uu____8013 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____8013
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
                  | uu____8161 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____8170 = tc_binders env1 bs  in
                  match uu____8170 with
                  | (bs1,envbody,g,uu____8200) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____8244 =
                    let uu____8245 = FStar_Syntax_Subst.compress t2  in
                    uu____8245.FStar_Syntax_Syntax.n  in
                  match uu____8244 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____8268 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8292 -> failwith "Impossible");
                       (let uu____8301 = tc_binders env1 bs  in
                        match uu____8301 with
                        | (bs1,envbody,g,uu____8333) ->
                            let uu____8334 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____8334 with
                             | (envbody1,uu____8362) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____8373;
                         FStar_Syntax_Syntax.pos = uu____8374;
                         FStar_Syntax_Syntax.vars = uu____8375;_},uu____8376)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8420 -> failwith "Impossible");
                       (let uu____8429 = tc_binders env1 bs  in
                        match uu____8429 with
                        | (bs1,envbody,g,uu____8461) ->
                            let uu____8462 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____8462 with
                             | (envbody1,uu____8490) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____8502) ->
                      let uu____8507 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____8507 with
                       | (uu____8548,bs1,bs',copt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____8591 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____8591 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____8700 c_expected2 body3
                               =
                               match uu____8700 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____8820 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env3, bs2, guard, uu____8820, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____8851 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____8851
                                           in
                                        let uu____8852 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env3, bs2, guard, uu____8852, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____8877 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____8877
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
                                               let uu____8929 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____8929 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____8952 =
                                                      check_binders env3
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____8952 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____9002 =
                                                           let uu____9033 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard'
                                                              in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____9033,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____9002
                                                           c_expected4 body3))
                                           | uu____9050 ->
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
                             let uu____9066 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____9066 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___87_9123 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___87_9123.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___87_9123.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___87_9123.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___87_9123.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___87_9123.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___87_9123.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___87_9123.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___87_9123.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___87_9123.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___87_9123.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___87_9123.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___87_9123.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___87_9123.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___87_9123.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___87_9123.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___87_9123.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___87_9123.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___87_9123.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___87_9123.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___87_9123.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___87_9123.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___87_9123.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___87_9123.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___87_9123.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___87_9123.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___87_9123.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___87_9123.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___87_9123.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___87_9123.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___87_9123.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___87_9123.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___87_9123.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___87_9123.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___87_9123.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___87_9123.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____9171  ->
                                     fun uu____9172  ->
                                       match (uu____9171, uu____9172) with
                                       | ((env2,letrec_binders),(l,t3,u_names))
                                           ->
                                           let uu____9234 =
                                             let uu____9241 =
                                               let uu____9242 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2
                                                  in
                                               FStar_All.pipe_right
                                                 uu____9242
                                                 FStar_Pervasives_Native.fst
                                                in
                                             tc_term uu____9241 t3  in
                                           (match uu____9234 with
                                            | (t4,uu____9264,uu____9265) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (u_names, t4)
                                                   in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____9275 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___88_9278 =
                                                             x  in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___88_9278.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___88_9278.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           })
                                                         in
                                                      uu____9275 ::
                                                        letrec_binders
                                                  | uu____9279 ->
                                                      letrec_binders
                                                   in
                                                (env3, lb))) (envbody1, []))
                              in
                           let uu____9284 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____9284 with
                            | (envbody,bs1,g,c,body2) ->
                                let uu____9338 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____9338 with
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
                  | uu____9384 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____9405 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2  in
                        as_function_typ true uu____9405
                      else
                        (let uu____9407 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____9407 with
                         | (uu____9446,bs1,uu____9448,c_opt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____9468 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____9468 with
          | (env1,topt) ->
              ((let uu____9488 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____9488
                then
                  let uu____9489 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____9489
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____9493 = expected_function_typ1 env1 topt body  in
                match uu____9493 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let uu____9533 =
                      let should_check_expected_effect =
                        let uu____9541 =
                          let uu____9548 =
                            let uu____9549 =
                              FStar_Syntax_Subst.compress body1  in
                            uu____9549.FStar_Syntax_Syntax.n  in
                          (c_opt, uu____9548)  in
                        match uu____9541 with
                        | (FStar_Pervasives_Native.None
                           ,FStar_Syntax_Syntax.Tm_ascribed
                           (uu____9554,(FStar_Util.Inr expected_c,uu____9556),uu____9557))
                            -> false
                        | uu____9606 -> true  in
                      let uu____9613 =
                        tc_term
                          (let uu___89_9622 = envbody  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___89_9622.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___89_9622.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___89_9622.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___89_9622.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___89_9622.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___89_9622.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___89_9622.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___89_9622.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___89_9622.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___89_9622.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___89_9622.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___89_9622.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___89_9622.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = false;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___89_9622.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq = use_eq;
                             FStar_TypeChecker_Env.is_iface =
                               (uu___89_9622.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___89_9622.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___89_9622.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___89_9622.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___89_9622.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___89_9622.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___89_9622.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___89_9622.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___89_9622.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___89_9622.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___89_9622.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___89_9622.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___89_9622.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth =
                               (uu___89_9622.FStar_TypeChecker_Env.synth);
                             FStar_TypeChecker_Env.splice =
                               (uu___89_9622.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___89_9622.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___89_9622.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___89_9622.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___89_9622.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___89_9622.FStar_TypeChecker_Env.dep_graph)
                           }) body1
                         in
                      match uu____9613 with
                      | (body2,cbody,guard_body) ->
                          let guard_body1 =
                            FStar_TypeChecker_Rel.solve_deferred_constraints
                              envbody guard_body
                             in
                          if should_check_expected_effect
                          then
                            let uu____9639 =
                              let uu____9646 =
                                let uu____9651 =
                                  FStar_Syntax_Syntax.lcomp_comp cbody  in
                                (body2, uu____9651)  in
                              check_expected_effect
                                (let uu___90_9654 = envbody  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___90_9654.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___90_9654.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___90_9654.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___90_9654.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___90_9654.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___90_9654.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___90_9654.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___90_9654.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___90_9654.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___90_9654.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___90_9654.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___90_9654.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___90_9654.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___90_9654.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___90_9654.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___90_9654.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___90_9654.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___90_9654.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___90_9654.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___90_9654.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___90_9654.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___90_9654.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___90_9654.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___90_9654.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___90_9654.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___90_9654.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___90_9654.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___90_9654.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___90_9654.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___90_9654.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___90_9654.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___90_9654.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___90_9654.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___90_9654.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___90_9654.FStar_TypeChecker_Env.dep_graph)
                                 }) c_opt uu____9646
                               in
                            (match uu____9639 with
                             | (body3,cbody1,guard) ->
                                 let uu____9664 =
                                   FStar_TypeChecker_Rel.conj_guard
                                     guard_body1 guard
                                    in
                                 (body3, cbody1, uu____9664))
                          else
                            (let uu____9666 =
                               FStar_Syntax_Syntax.lcomp_comp cbody  in
                             (body2, uu____9666, guard_body1))
                       in
                    (match uu____9533 with
                     | (body2,cbody,guard) ->
                         let guard1 =
                           let uu____9677 =
                             env1.FStar_TypeChecker_Env.top_level ||
                               (let uu____9679 =
                                  FStar_TypeChecker_Env.should_verify env1
                                   in
                                Prims.op_Negation uu____9679)
                              in
                           if uu____9677
                           then
                             let uu____9680 =
                               FStar_TypeChecker_Rel.conj_guard g guard  in
                             FStar_TypeChecker_Rel.discharge_guard envbody
                               uu____9680
                           else
                             (let guard1 =
                                let uu____9683 =
                                  FStar_TypeChecker_Rel.conj_guard g guard
                                   in
                                FStar_TypeChecker_Rel.close_guard env1
                                  (FStar_List.append bs1 letrec_binders)
                                  uu____9683
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
                         let uu____9692 =
                           match tfun_opt with
                           | FStar_Pervasives_Native.Some t ->
                               let t1 = FStar_Syntax_Subst.compress t  in
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_arrow uu____9713 ->
                                    (e, t1, guard1)
                                | uu____9726 ->
                                    let uu____9727 =
                                      FStar_TypeChecker_Util.check_and_ascribe
                                        env1 e tfun_computed t1
                                       in
                                    (match uu____9727 with
                                     | (e1,guard') ->
                                         let uu____9740 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 guard'
                                            in
                                         (e1, t1, uu____9740)))
                           | FStar_Pervasives_Native.None  ->
                               (e, tfun_computed, guard1)
                            in
                         (match uu____9692 with
                          | (e1,tfun,guard2) ->
                              let c = FStar_Syntax_Syntax.mk_Total tfun  in
                              let uu____9753 =
                                let uu____9758 =
                                  FStar_Syntax_Util.lcomp_of_comp c  in
                                FStar_TypeChecker_Util.strengthen_precondition
                                  FStar_Pervasives_Native.None env1 e1
                                  uu____9758 guard2
                                 in
                              (match uu____9753 with
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
              (let uu____9803 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____9803
               then
                 let uu____9804 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____9805 = FStar_Syntax_Print.term_to_string thead  in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____9804
                   uu____9805
               else ());
              (let monadic_application uu____9862 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____9862 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ
                        in
                     let cres1 =
                       let uu___91_9921 = cres  in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___91_9921.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___91_9921.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp_thunk =
                           (uu___91_9921.FStar_Syntax_Syntax.comp_thunk)
                       }  in
                     let uu____9922 =
                       match bs with
                       | [] ->
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard
                              in
                           (cres1, g)
                       | uu____9936 ->
                           let g =
                             let uu____9944 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard
                                in
                             FStar_All.pipe_right uu____9944
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env)
                              in
                           let uu____9945 =
                             let uu____9946 =
                               let uu____9949 =
                                 let uu____9950 =
                                   FStar_Syntax_Syntax.lcomp_comp cres1  in
                                 FStar_Syntax_Util.arrow bs uu____9950  in
                               FStar_Syntax_Syntax.mk_Total uu____9949  in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____9946
                              in
                           (uu____9945, g)
                        in
                     (match uu____9922 with
                      | (cres2,guard1) ->
                          ((let uu____9964 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low
                               in
                            if uu____9964
                            then
                              let uu____9965 =
                                FStar_Syntax_Print.lcomp_to_string cres2  in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____9965
                            else ());
                           (let cres3 =
                              let head_is_pure_and_some_arg_is_effectful =
                                (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                   chead1)
                                  &&
                                  (FStar_Util.for_some
                                     (fun uu____9981  ->
                                        match uu____9981 with
                                        | (uu____9990,uu____9991,lc) ->
                                            (let uu____9999 =
                                               FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                 lc
                                                in
                                             Prims.op_Negation uu____9999) ||
                                              (FStar_TypeChecker_Util.should_not_inline_lc
                                                 lc)) arg_comps_rev)
                                 in
                              let term =
                                FStar_Syntax_Syntax.mk_Tm_app head2
                                  (FStar_List.rev arg_rets_rev)
                                  FStar_Pervasives_Native.None
                                  head2.FStar_Syntax_Syntax.pos
                                 in
                              let uu____10009 =
                                (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                   cres2)
                                  && head_is_pure_and_some_arg_is_effectful
                                 in
                              if uu____10009
                              then
                                ((let uu____10011 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme
                                     in
                                  if uu____10011
                                  then
                                    let uu____10012 =
                                      FStar_Syntax_Print.term_to_string term
                                       in
                                    FStar_Util.print1
                                      "(a) Monadic app: Return inserted in monadic application: %s\n"
                                      uu____10012
                                  else ());
                                 FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                   env term cres2)
                              else
                                ((let uu____10016 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme
                                     in
                                  if uu____10016
                                  then
                                    let uu____10017 =
                                      FStar_Syntax_Print.term_to_string term
                                       in
                                    FStar_Util.print1
                                      "(a) Monadic app: No return inserted in monadic application: %s\n"
                                      uu____10017
                                  else ());
                                 cres2)
                               in
                            let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____10041  ->
                                     match uu____10041 with
                                     | ((e,q),x,c) ->
                                         ((let uu____10067 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____10067
                                           then
                                             let uu____10068 =
                                               match x with
                                               | FStar_Pervasives_Native.None
                                                    -> "_"
                                               | FStar_Pervasives_Native.Some
                                                   x1 ->
                                                   FStar_Syntax_Print.bv_to_string
                                                     x1
                                                in
                                             let uu____10070 =
                                               FStar_Syntax_Print.term_to_string
                                                 e
                                                in
                                             FStar_Util.print2
                                               "(b) Monadic app: Binding argument %s : %s\n"
                                               uu____10068 uu____10070
                                           else ());
                                          (let uu____10072 =
                                             FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                               c
                                              in
                                           if uu____10072
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
                              (let uu____10080 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme
                                  in
                               if uu____10080
                               then
                                 let uu____10081 =
                                   FStar_Syntax_Print.term_to_string head2
                                    in
                                 FStar_Util.print1
                                   "(c) Monadic app: Binding head %s "
                                   uu____10081
                               else ());
                              (let uu____10083 =
                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                   chead1
                                  in
                               if uu____10083
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
                              let uu____10091 =
                                let uu____10092 =
                                  FStar_Syntax_Subst.compress head2  in
                                uu____10092.FStar_Syntax_Syntax.n  in
                              match uu____10091 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____10096 -> false  in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____10117  ->
                                         match uu____10117 with
                                         | (arg,uu____10131,uu____10132) ->
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
                                (let uu____10142 =
                                   let map_fun uu____10204 =
                                     match uu____10204 with
                                     | ((e,q),uu____10239,c) ->
                                         let uu____10249 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c
                                            in
                                         if uu____10249
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
                                            let uu____10299 =
                                              let uu____10304 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              (uu____10304, q)  in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____10299))
                                      in
                                   let uu____10333 =
                                     let uu____10358 =
                                       let uu____10381 =
                                         let uu____10396 =
                                           let uu____10405 =
                                             FStar_Syntax_Syntax.as_arg head2
                                              in
                                           (uu____10405,
                                             FStar_Pervasives_Native.None,
                                             chead1)
                                            in
                                         uu____10396 :: arg_comps_rev  in
                                       FStar_List.map map_fun uu____10381  in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____10358
                                      in
                                   match uu____10333 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____10578 =
                                         let uu____10579 =
                                           FStar_List.hd reverse_args  in
                                         FStar_Pervasives_Native.fst
                                           uu____10579
                                          in
                                       let uu____10588 =
                                         let uu____10595 =
                                           FStar_List.tl reverse_args  in
                                         FStar_List.rev uu____10595  in
                                       (lifted_args, uu____10578,
                                         uu____10588)
                                    in
                                 match uu____10142 with
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
                                     let bind_lifted_args e uu___65_10698 =
                                       match uu___65_10698 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1
                                               [] e1.FStar_Syntax_Syntax.pos
                                              in
                                           let letbinding =
                                             let uu____10755 =
                                               let uu____10758 =
                                                 let uu____10759 =
                                                   let uu____10772 =
                                                     let uu____10773 =
                                                       let uu____10774 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x
                                                          in
                                                       [uu____10774]  in
                                                     FStar_Syntax_Subst.close
                                                       uu____10773 e
                                                      in
                                                   ((false, [lb]),
                                                     uu____10772)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____10759
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10758
                                                in
                                             uu____10755
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
                            let uu____10804 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp2
                                guard1
                               in
                            match uu____10804 with
                            | (comp3,g) ->
                                ((let uu____10820 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme
                                     in
                                  if uu____10820
                                  then
                                    let uu____10821 =
                                      FStar_Syntax_Print.term_to_string app
                                       in
                                    let uu____10822 =
                                      FStar_Syntax_Print.lcomp_to_string
                                        comp3
                                       in
                                    FStar_Util.print2
                                      "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                      uu____10821 uu____10822
                                  else ());
                                 (app, comp3, g)))))
                  in
               let rec tc_args head_info uu____10898 bs args1 =
                 match uu____10898 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____11041))::rest,
                         (uu____11043,FStar_Pervasives_Native.None )::uu____11044)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          let uu____11095 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____11095 with
                           | (varg,uu____11115,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1
                                  in
                               let arg =
                                 let uu____11137 =
                                   FStar_Syntax_Syntax.as_implicit true  in
                                 (varg, uu____11137)  in
                               let uu____11138 =
                                 let uu____11173 =
                                   let uu____11188 =
                                     let uu____11201 =
                                       let uu____11202 =
                                         FStar_Syntax_Syntax.mk_Total t1  in
                                       FStar_All.pipe_right uu____11202
                                         FStar_Syntax_Util.lcomp_of_comp
                                        in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____11201)
                                      in
                                   uu____11188 :: outargs  in
                                 let uu____11221 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g
                                    in
                                 (subst2, uu____11173, (arg :: arg_rets),
                                   uu____11221, fvs)
                                  in
                               tc_args head_info uu____11138 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____11313),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11314)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____11327 ->
                                let uu____11336 =
                                  let uu____11341 =
                                    let uu____11342 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____11343 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____11344 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____11345 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____11342 uu____11343 uu____11344
                                      uu____11345
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____11341)
                                   in
                                FStar_Errors.raise_error uu____11336
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let x1 =
                              let uu___92_11348 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___92_11348.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___92_11348.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____11350 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____11350
                             then
                               let uu____11351 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____11351
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
                               let uu___93_11356 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___93_11356.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___93_11356.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___93_11356.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___93_11356.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___93_11356.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___93_11356.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___93_11356.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___93_11356.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___93_11356.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___93_11356.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___93_11356.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___93_11356.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___93_11356.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___93_11356.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___93_11356.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___93_11356.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___93_11356.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___93_11356.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___93_11356.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___93_11356.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___93_11356.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___93_11356.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___93_11356.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___93_11356.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___93_11356.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___93_11356.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___93_11356.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___93_11356.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___93_11356.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___93_11356.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___93_11356.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___93_11356.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___93_11356.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___93_11356.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___93_11356.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             (let uu____11358 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High
                                 in
                              if uu____11358
                              then
                                let uu____11359 =
                                  FStar_Syntax_Print.tag_of_term e  in
                                let uu____11360 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____11361 =
                                  FStar_Syntax_Print.term_to_string targ1  in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____11359 uu____11360 uu____11361
                              else ());
                             (let uu____11363 = tc_term env2 e  in
                              match uu____11363 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e
                                     in
                                  let arg = (e1, aq)  in
                                  let xterm =
                                    let uu____11398 =
                                      let uu____11401 =
                                        let uu____11408 =
                                          FStar_Syntax_Syntax.bv_to_name x1
                                           in
                                        FStar_Syntax_Syntax.as_arg
                                          uu____11408
                                         in
                                      FStar_Pervasives_Native.fst uu____11401
                                       in
                                    (uu____11398, aq)  in
                                  let uu____11415 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name)
                                     in
                                  if uu____11415
                                  then
                                    let subst2 =
                                      let uu____11423 = FStar_List.hd bs  in
                                      maybe_extend_subst subst1 uu____11423
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
                      | (uu____11549,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____11581) ->
                          let uu____11624 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____11624 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____11658 =
                                     FStar_Syntax_Subst.compress tres  in
                                   FStar_All.pipe_right uu____11658
                                     FStar_Syntax_Util.unrefine
                                    in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____11683 =
                                       FStar_Syntax_Subst.open_comp bs1 cres'
                                        in
                                     (match uu____11683 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            let uu____11705 =
                                              FStar_Syntax_Util.lcomp_of_comp
                                                cres'1
                                               in
                                            (head2, chead1, ghead1,
                                              uu____11705)
                                             in
                                          ((let uu____11707 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low
                                               in
                                            if uu____11707
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
                                 | uu____11749 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2
                                          in
                                       let uu____11755 =
                                         let uu____11756 =
                                           FStar_Syntax_Subst.compress tres3
                                            in
                                         uu____11756.FStar_Syntax_Syntax.n
                                          in
                                       match uu____11755 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____11759;
                                              FStar_Syntax_Syntax.index =
                                                uu____11760;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},uu____11762)
                                           -> norm_tres tres4
                                       | uu____11769 -> tres3  in
                                     let uu____11770 = norm_tres tres1  in
                                     aux true uu____11770
                                 | uu____11771 ->
                                     let uu____11772 =
                                       let uu____11777 =
                                         let uu____11778 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead
                                            in
                                         let uu____11779 =
                                           FStar_Util.string_of_int n_args
                                            in
                                         FStar_Util.format2
                                           "Too many arguments to function of type %s; got %s arguments"
                                           uu____11778 uu____11779
                                          in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____11777)
                                        in
                                     let uu____11786 =
                                       FStar_Syntax_Syntax.argpos arg  in
                                     FStar_Errors.raise_error uu____11772
                                       uu____11786
                                  in
                               aux false chead1.FStar_Syntax_Syntax.res_typ))
                  in
               let rec check_function_app tf =
                 let uu____11805 =
                   let uu____11806 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____11806.FStar_Syntax_Syntax.n  in
                 match uu____11805 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____11817 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____11918 = tc_term env1 e  in
                           (match uu____11918 with
                            | (e1,c,g_e) ->
                                let uu____11940 = tc_args1 env1 tl1  in
                                (match uu____11940 with
                                 | (args2,comps,g_rest) ->
                                     let uu____11980 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest
                                        in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____11980)))
                        in
                     let uu____12001 = tc_args1 env args  in
                     (match uu____12001 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____12038 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____12076  ->
                                      match uu____12076 with
                                      | (uu____12089,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None)))
                               in
                            FStar_Syntax_Util.null_binders_of_tks uu____12038
                             in
                          let ml_or_tot t r1 =
                            let uu____12106 = FStar_Options.ml_ish ()  in
                            if uu____12106
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t  in
                          let cres =
                            let uu____12109 =
                              let uu____12112 =
                                let uu____12113 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____12113
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_uvar env uu____12112
                               in
                            ml_or_tot uu____12109 r  in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                          ((let uu____12126 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            if uu____12126
                            then
                              let uu____12127 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____12128 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____12129 =
                                FStar_Syntax_Print.term_to_string bs_cres  in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____12127 uu____12128 uu____12129
                            else ());
                           (let uu____12132 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres  in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____12132);
                           (let comp =
                              let uu____12134 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres
                                 in
                              FStar_List.fold_right
                                (fun uu____12145  ->
                                   fun out  ->
                                     match uu____12145 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____12134
                               in
                            let uu____12159 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r
                               in
                            let uu____12162 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args
                               in
                            (uu____12159, comp, uu____12162))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____12165;
                        FStar_Syntax_Syntax.pos = uu____12166;
                        FStar_Syntax_Syntax.vars = uu____12167;_},uu____12168)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____12289 = tc_term env1 e  in
                           (match uu____12289 with
                            | (e1,c,g_e) ->
                                let uu____12311 = tc_args1 env1 tl1  in
                                (match uu____12311 with
                                 | (args2,comps,g_rest) ->
                                     let uu____12351 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest
                                        in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____12351)))
                        in
                     let uu____12372 = tc_args1 env args  in
                     (match uu____12372 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____12409 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____12447  ->
                                      match uu____12447 with
                                      | (uu____12460,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None)))
                               in
                            FStar_Syntax_Util.null_binders_of_tks uu____12409
                             in
                          let ml_or_tot t r1 =
                            let uu____12477 = FStar_Options.ml_ish ()  in
                            if uu____12477
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t  in
                          let cres =
                            let uu____12480 =
                              let uu____12483 =
                                let uu____12484 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____12484
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_uvar env uu____12483
                               in
                            ml_or_tot uu____12480 r  in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres  in
                          ((let uu____12497 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme
                               in
                            if uu____12497
                            then
                              let uu____12498 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____12499 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____12500 =
                                FStar_Syntax_Print.term_to_string bs_cres  in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____12498 uu____12499 uu____12500
                            else ());
                           (let uu____12503 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres  in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____12503);
                           (let comp =
                              let uu____12505 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres
                                 in
                              FStar_List.fold_right
                                (fun uu____12516  ->
                                   fun out  ->
                                     match uu____12516 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____12505
                               in
                            let uu____12530 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r
                               in
                            let uu____12533 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args
                               in
                            (uu____12530, comp, uu____12533))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____12554 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____12554 with
                      | (bs1,c1) ->
                          let head_info =
                            let uu____12578 =
                              FStar_Syntax_Util.lcomp_of_comp c1  in
                            (head1, chead, ghead, uu____12578)  in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____12620) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____12626,uu____12627) -> check_function_app t
                 | uu____12668 ->
                     let uu____12669 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____12669
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
                  let uu____12743 =
                    FStar_List.fold_left2
                      (fun uu____12786  ->
                         fun uu____12787  ->
                           fun uu____12788  ->
                             match (uu____12786, uu____12787, uu____12788)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                        "Inconsistent implicit qualifiers")
                                      e.FStar_Syntax_Syntax.pos
                                  else ();
                                  (let uu____12856 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____12856 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____12874 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____12874 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____12878 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____12878)
                                              &&
                                              (let uu____12880 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name
                                                  in
                                               Prims.op_Negation uu____12880))
                                          in
                                       let uu____12881 =
                                         let uu____12890 =
                                           let uu____12899 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____12899]  in
                                         FStar_List.append seen uu____12890
                                          in
                                       let uu____12906 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1
                                          in
                                       (uu____12881, uu____12906, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____12743 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____12942 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____12942
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c  in
                       let uu____12944 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____12944 with | (c2,g) -> (e, c2, g)))
              | uu____12961 ->
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
        let uu____13003 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____13003 with
        | (pattern,when_clause,branch_exp) ->
            let uu____13047 = branch1  in
            (match uu____13047 with
             | (cpat,uu____13087,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let tc_annot env1 t =
                     let uu____13154 = FStar_Syntax_Util.type_u ()  in
                     match uu____13154 with
                     | (tu,u) ->
                         let uu____13165 =
                           tc_check_tot_or_gtot_term env1 t tu  in
                         (match uu____13165 with
                          | (t1,uu____13177,g) -> (t1, g))
                      in
                   let uu____13179 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0
                       tc_annot
                      in
                   match uu____13179 with
                   | (pat_bvs1,exp,guard_pat_annots,p) ->
                       ((let uu____13213 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High
                            in
                         if uu____13213
                         then
                           let uu____13214 =
                             FStar_Syntax_Print.pat_to_string p0  in
                           let uu____13215 =
                             FStar_Syntax_Print.pat_to_string p  in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____13214 uu____13215
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1
                            in
                         let uu____13218 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env
                            in
                         match uu____13218 with
                         | (env1,uu____13240) ->
                             let env11 =
                               let uu___94_13246 = env1  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___94_13246.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___94_13246.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___94_13246.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___94_13246.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___94_13246.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___94_13246.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___94_13246.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___94_13246.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___94_13246.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___94_13246.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___94_13246.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___94_13246.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___94_13246.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___94_13246.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___94_13246.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___94_13246.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___94_13246.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___94_13246.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___94_13246.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___94_13246.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___94_13246.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___94_13246.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___94_13246.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___94_13246.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___94_13246.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___94_13246.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___94_13246.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___94_13246.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___94_13246.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___94_13246.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___94_13246.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___94_13246.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___94_13246.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___94_13246.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___94_13246.FStar_TypeChecker_Env.dep_graph)
                               }  in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t  in
                             ((let uu____13249 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High
                                  in
                               if uu____13249
                               then
                                 let uu____13250 =
                                   FStar_Syntax_Print.term_to_string exp  in
                                 let uu____13251 =
                                   FStar_Syntax_Print.term_to_string pat_t
                                    in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____13250 uu____13251
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t
                                  in
                               let uu____13254 =
                                 tc_tot_or_gtot_term env12 exp  in
                               match uu____13254 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___95_13279 = g  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___95_13279.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___95_13279.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___95_13279.FStar_TypeChecker_Env.implicits)
                                     }  in
                                   let uu____13280 =
                                     let uu____13281 =
                                       FStar_TypeChecker_Rel.teq_nosmt env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t
                                        in
                                     if uu____13281
                                     then
                                       let env13 =
                                         FStar_TypeChecker_Env.set_range
                                           env12 exp1.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____13283 =
                                         FStar_TypeChecker_Rel.discharge_guard_no_smt
                                           env13 g1
                                          in
                                       FStar_All.pipe_right uu____13283
                                         FStar_TypeChecker_Rel.resolve_implicits
                                     else
                                       (let uu____13285 =
                                          let uu____13290 =
                                            let uu____13291 =
                                              FStar_Syntax_Print.term_to_string
                                                lc.FStar_Syntax_Syntax.res_typ
                                               in
                                            let uu____13292 =
                                              FStar_Syntax_Print.term_to_string
                                                expected_pat_t
                                               in
                                            FStar_Util.format2
                                              "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                              uu____13291 uu____13292
                                             in
                                          (FStar_Errors.Fatal_MismatchedPatternType,
                                            uu____13290)
                                           in
                                        FStar_Errors.raise_error uu____13285
                                          exp1.FStar_Syntax_Syntax.pos)
                                      in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1
                                      in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp  in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t
                                      in
                                   ((let uu____13309 =
                                       let uu____13310 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2
                                          in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____13310
                                        in
                                     if uu____13309
                                     then
                                       let unresolved =
                                         let uu____13322 =
                                           FStar_Util.set_difference uvs1
                                             uvs2
                                            in
                                         FStar_All.pipe_right uu____13322
                                           FStar_Util.set_elements
                                          in
                                       let uu____13349 =
                                         let uu____13354 =
                                           let uu____13355 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env norm_exp
                                              in
                                           let uu____13356 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env expected_pat_t
                                              in
                                           let uu____13357 =
                                             let uu____13358 =
                                               FStar_All.pipe_right
                                                 unresolved
                                                 (FStar_List.map
                                                    (fun uu____13376  ->
                                                       match uu____13376 with
                                                       | (u,uu____13382) ->
                                                           FStar_Syntax_Print.uvar_to_string
                                                             u))
                                                in
                                             FStar_All.pipe_right uu____13358
                                               (FStar_String.concat ", ")
                                              in
                                           FStar_Util.format3
                                             "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                             uu____13355 uu____13356
                                             uu____13357
                                            in
                                         (FStar_Errors.Fatal_UnresolvedPatternVar,
                                           uu____13354)
                                          in
                                       FStar_Errors.raise_error uu____13349
                                         p.FStar_Syntax_Syntax.p
                                     else ());
                                    (let uu____13387 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High
                                        in
                                     if uu____13387
                                     then
                                       let uu____13388 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1
                                          in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____13388
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
                 let uu____13397 =
                   let uu____13404 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____13404
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____13397 with
                  | (scrutinee_env,uu____13436) ->
                      let uu____13441 = tc_pat true pat_t pattern  in
                      (match uu____13441 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,guard_pat_annots,norm_pat_exp)
                           ->
                           let uu____13490 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____13512 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____13512
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____13526 =
                                      let uu____13533 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____13533 e  in
                                    match uu____13526 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____13490 with
                            | (when_clause1,g_when) ->
                                let uu____13575 = tc_term pat_env branch_exp
                                   in
                                (match uu____13575 with
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
                                           let uu____13616 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool
                                              in
                                           FStar_All.pipe_left
                                             (fun _0_41  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_41) uu____13616
                                        in
                                     let uu____13619 =
                                       let eqs =
                                         let uu____13637 =
                                           let uu____13638 =
                                             FStar_TypeChecker_Env.should_verify
                                               env
                                              in
                                           Prims.op_Negation uu____13638  in
                                         if uu____13637
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp
                                               in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____13645 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____13662 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____13663 ->
                                                FStar_Pervasives_Native.None
                                            | uu____13664 ->
                                                let uu____13665 =
                                                  let uu____13666 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____13666 pat_t
                                                    scrutinee_tm e
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____13665)
                                          in
                                       let uu____13667 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch1
                                          in
                                       match uu____13667 with
                                       | (c1,g_branch2) ->
                                           let uu____13690 =
                                             match (eqs, when_condition) with
                                             | uu____13703 when
                                                 let uu____13712 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env
                                                    in
                                                 Prims.op_Negation
                                                   uu____13712
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
                                                 let uu____13724 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf
                                                    in
                                                 let uu____13725 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when
                                                    in
                                                 (uu____13724, uu____13725)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f
                                                    in
                                                 let g_fw =
                                                   let uu____13734 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w
                                                      in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____13734
                                                    in
                                                 let uu____13735 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw
                                                    in
                                                 let uu____13736 =
                                                   let uu____13737 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f
                                                      in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____13737 g_when
                                                    in
                                                 (uu____13735, uu____13736)
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
                                                 let uu____13745 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w
                                                    in
                                                 (uu____13745, g_when)
                                              in
                                           (match uu____13690 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1
                                                   in
                                                let maybe_return_c_weak
                                                  should_return =
                                                  let c_weak1 =
                                                    let uu____13770 =
                                                      should_return &&
                                                        (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                           c_weak)
                                                       in
                                                    if uu____13770
                                                    then
                                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                        env branch_exp1
                                                        c_weak
                                                    else c_weak  in
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak1
                                                   in
                                                let uu____13772 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak
                                                   in
                                                ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                  (c_weak.FStar_Syntax_Syntax.cflags),
                                                  maybe_return_c_weak,
                                                  uu____13772, g_branch2))
                                        in
                                     (match uu____13619 with
                                      | (effect_label,cflags,maybe_return_c,g_when1,g_branch2)
                                          ->
                                          let branch_guard =
                                            let uu____13815 =
                                              let uu____13816 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____13816
                                               in
                                            if uu____13815
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____13846 =
                                                     let uu____13847 =
                                                       let uu____13848 =
                                                         let uu____13851 =
                                                           let uu____13858 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v
                                                              in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____13858
                                                            in
                                                         FStar_Pervasives_Native.snd
                                                           uu____13851
                                                          in
                                                       FStar_List.length
                                                         uu____13848
                                                        in
                                                     uu____13847 >
                                                       (Prims.parse_int "1")
                                                      in
                                                   if uu____13846
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v
                                                        in
                                                     let uu____13864 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator
                                                        in
                                                     match uu____13864 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____13885 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         let disc1 =
                                                           let uu____13900 =
                                                             let uu____13901
                                                               =
                                                               let uu____13902
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2
                                                                  in
                                                               [uu____13902]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____13901
                                                              in
                                                           uu____13900
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                            in
                                                         let uu____13905 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool
                                                            in
                                                         [uu____13905]
                                                   else []  in
                                                 let fail uu____13910 =
                                                   let uu____13911 =
                                                     let uu____13912 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos
                                                        in
                                                     let uu____13913 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1
                                                        in
                                                     let uu____13914 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1
                                                        in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____13912
                                                       uu____13913
                                                       uu____13914
                                                      in
                                                   failwith uu____13911  in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____13925) ->
                                                       head_constructor t1
                                                   | uu____13930 -> fail ()
                                                    in
                                                 let pat_exp2 =
                                                   let uu____13932 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____13932
                                                     FStar_Syntax_Util.unmeta
                                                    in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____13935 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____13952;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____13953;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____13954;_},uu____13955)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____13992 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c1 ->
                                                     let uu____13994 =
                                                       let uu____13995 =
                                                         tc_constant env
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c1
                                                          in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____13995
                                                         scrutinee_tm1
                                                         pat_exp2
                                                        in
                                                     [uu____13994]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____13996 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____14004 =
                                                       let uu____14005 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____14005
                                                        in
                                                     if uu____14004
                                                     then []
                                                     else
                                                       (let uu____14009 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____14009)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____14012 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2
                                                        in
                                                     let uu____14014 =
                                                       let uu____14015 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____14015
                                                        in
                                                     if uu____14014
                                                     then []
                                                     else
                                                       (let uu____14019 =
                                                          head_constructor
                                                            pat_exp2
                                                           in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____14019)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1
                                                        in
                                                     let uu____14045 =
                                                       let uu____14046 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       Prims.op_Negation
                                                         uu____14046
                                                        in
                                                     if uu____14045
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____14053 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____14085
                                                                     ->
                                                                    match uu____14085
                                                                    with
                                                                    | 
                                                                    (ei,uu____14095)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let uu____14101
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    (match uu____14101
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____14122
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____14136
                                                                    =
                                                                    let uu____14137
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____14138
                                                                    =
                                                                    let uu____14139
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1
                                                                     in
                                                                    [uu____14139]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____14137
                                                                    uu____14138
                                                                     in
                                                                    uu____14136
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei)))
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14053
                                                            FStar_List.flatten
                                                           in
                                                        let uu____14148 =
                                                          discriminate
                                                            scrutinee_tm1 f
                                                           in
                                                        FStar_List.append
                                                          uu____14148
                                                          sub_term_guards)
                                                 | uu____14151 -> []  in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____14163 =
                                                   let uu____14164 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____14164
                                                    in
                                                 if uu____14163
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____14167 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____14167
                                                       in
                                                    let uu____14172 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    match uu____14172 with
                                                    | (k,uu____14178) ->
                                                        let uu____14179 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k
                                                           in
                                                        (match uu____14179
                                                         with
                                                         | (t1,uu____14187,uu____14188)
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
                                          ((let uu____14194 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High
                                               in
                                            if uu____14194
                                            then
                                              let uu____14195 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard
                                                 in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____14195
                                            else ());
                                           (let uu____14197 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1)
                                               in
                                            (uu____14197, branch_guard,
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
          let uu____14227 = check_let_bound_def true env1 lb  in
          (match uu____14227 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____14249 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____14266 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____14266, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____14269 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____14269
                        FStar_TypeChecker_Rel.resolve_implicits
                       in
                    let uu____14273 =
                      let uu____14286 =
                        let uu____14301 =
                          let uu____14310 =
                            let uu____14321 =
                              FStar_Syntax_Syntax.lcomp_comp c1  in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____14321)
                             in
                          [uu____14310]  in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____14301
                         in
                      FStar_List.hd uu____14286  in
                    match uu____14273 with
                    | (uu____14366,univs1,e11,c11,gvs) ->
                        let g12 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Rel.map_guard g11)
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta;
                               FStar_TypeChecker_Normalize.NoDeltaSteps;
                               FStar_TypeChecker_Normalize.CompressUvars;
                               FStar_TypeChecker_Normalize.NoFullNorm;
                               FStar_TypeChecker_Normalize.Exclude
                                 FStar_TypeChecker_Normalize.Zeta] env1)
                           in
                        let g13 =
                          FStar_TypeChecker_Rel.abstract_guard_n gvs g12  in
                        let uu____14379 = FStar_Syntax_Util.lcomp_of_comp c11
                           in
                        (g13, e11, univs1, uu____14379))
                  in
               (match uu____14249 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____14390 =
                      let uu____14397 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____14397
                      then
                        let uu____14404 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____14404 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____14427 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____14427
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____14428 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____14428, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____14438 =
                              FStar_Syntax_Syntax.lcomp_comp c11  in
                            FStar_All.pipe_right uu____14438
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm] env1)
                             in
                          let e21 =
                            let uu____14442 =
                              FStar_Syntax_Util.is_pure_comp c  in
                            if uu____14442
                            then e2
                            else
                              ((let uu____14447 =
                                  FStar_TypeChecker_Env.get_range env1  in
                                FStar_Errors.log_issue uu____14447
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
                    (match uu____14390 with
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
                         let uu____14468 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos
                            in
                         let uu____14481 =
                           FStar_Syntax_Util.lcomp_of_comp cres  in
                         (uu____14468, uu____14481,
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____14484 -> failwith "Impossible"

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
            let uu___96_14515 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___96_14515.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___96_14515.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___96_14515.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___96_14515.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___96_14515.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___96_14515.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___96_14515.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___96_14515.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___96_14515.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___96_14515.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___96_14515.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___96_14515.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___96_14515.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___96_14515.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___96_14515.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___96_14515.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___96_14515.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___96_14515.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___96_14515.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___96_14515.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___96_14515.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___96_14515.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___96_14515.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___96_14515.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___96_14515.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___96_14515.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___96_14515.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___96_14515.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___96_14515.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.splice =
                (uu___96_14515.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___96_14515.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___96_14515.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___96_14515.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___96_14515.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___96_14515.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____14516 =
            let uu____14527 =
              let uu____14528 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____14528 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____14527 lb  in
          (match uu____14516 with
           | (e1,uu____14550,c1,g1,annotated) ->
               ((let uu____14555 =
                   (FStar_Util.for_some
                      (FStar_Syntax_Util.is_fvar
                         FStar_Parser_Const.inline_let_attr)
                      lb.FStar_Syntax_Syntax.lbattrs)
                     &&
                     (let uu____14557 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp c1  in
                      Prims.op_Negation uu____14557)
                    in
                 if uu____14555
                 then
                   let uu____14558 =
                     let uu____14563 =
                       let uu____14564 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____14565 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____14564 uu____14565
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____14563)
                      in
                   FStar_Errors.raise_error uu____14558
                     e1.FStar_Syntax_Syntax.pos
                 else ());
                (let x =
                   let uu___97_14568 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___97_14568.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___97_14568.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_Syntax_Syntax.res_typ)
                   }  in
                 let uu____14569 =
                   let uu____14574 =
                     let uu____14575 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____14575]  in
                   FStar_Syntax_Subst.open_term uu____14574 e2  in
                 match uu____14569 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____14595 = tc_term env_x e21  in
                     (match uu____14595 with
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
                            let uu____14620 =
                              let uu____14623 =
                                let uu____14624 =
                                  let uu____14637 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____14637)  in
                                FStar_Syntax_Syntax.Tm_let uu____14624  in
                              FStar_Syntax_Syntax.mk uu____14623  in
                            uu____14620 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_Syntax_Syntax.eff_name
                              cres.FStar_Syntax_Syntax.res_typ
                             in
                          let x_eq_e1 =
                            let uu____14651 =
                              let uu____14652 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_Syntax_Syntax.res_typ
                                 in
                              let uu____14653 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____14652
                                c1.FStar_Syntax_Syntax.res_typ uu____14653
                                e11
                               in
                            FStar_All.pipe_left
                              (fun _0_42  ->
                                 FStar_TypeChecker_Common.NonTrivial _0_42)
                              uu____14651
                             in
                          let g21 =
                            let uu____14655 =
                              let uu____14656 =
                                FStar_TypeChecker_Rel.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Rel.imp_guard uu____14656 g2
                               in
                            FStar_TypeChecker_Rel.close_guard env2 xb
                              uu____14655
                             in
                          let guard = FStar_TypeChecker_Rel.conj_guard g1 g21
                             in
                          let uu____14658 =
                            let uu____14659 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____14659  in
                          if uu____14658
                          then
                            let tt =
                              let uu____14669 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____14669
                                FStar_Option.get
                               in
                            ((let uu____14675 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____14675
                              then
                                let uu____14676 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____14677 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____14676 uu____14677
                              else ());
                             (e4, cres, guard))
                          else
                            (let t =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1] cres.FStar_Syntax_Syntax.res_typ
                                in
                             (let uu____14682 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____14682
                              then
                                let uu____14683 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____14684 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "Checked %s has no escaping types; normalized to %s\n"
                                  uu____14683 uu____14684
                              else ());
                             (e4,
                               ((let uu___98_14687 = cres  in
                                 {
                                   FStar_Syntax_Syntax.eff_name =
                                     (uu___98_14687.FStar_Syntax_Syntax.eff_name);
                                   FStar_Syntax_Syntax.res_typ = t;
                                   FStar_Syntax_Syntax.cflags =
                                     (uu___98_14687.FStar_Syntax_Syntax.cflags);
                                   FStar_Syntax_Syntax.comp_thunk =
                                     (uu___98_14687.FStar_Syntax_Syntax.comp_thunk)
                                 })), guard))))))
      | uu____14688 -> failwith "Impossible"

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
          let uu____14720 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____14720 with
           | (lbs1,e21) ->
               let uu____14739 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____14739 with
                | (env0,topt) ->
                    let uu____14758 = build_let_rec_env true env0 lbs1  in
                    (match uu____14758 with
                     | (lbs2,rec_env) ->
                         let uu____14777 = check_let_recs rec_env lbs2  in
                         (match uu____14777 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____14797 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs
                                   in
                                FStar_All.pipe_right uu____14797
                                  FStar_TypeChecker_Rel.resolve_implicits
                                 in
                              let all_lb_names =
                                let uu____14803 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____14803
                                  (fun _0_43  ->
                                     FStar_Pervasives_Native.Some _0_43)
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
                                     let uu____14852 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____14892 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____14892)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____14852
                                      in
                                   FStar_List.map2
                                     (fun uu____14926  ->
                                        fun lb  ->
                                          match uu____14926 with
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
                                let uu____14974 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____14974
                                 in
                              let uu____14979 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____14979 with
                               | (lbs5,e22) ->
                                   ((let uu____14999 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____14999
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____15000 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____15000, cres,
                                       FStar_TypeChecker_Rel.trivial_guard))))))))
      | uu____15013 -> failwith "Impossible"

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
          let uu____15045 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____15045 with
           | (lbs1,e21) ->
               let uu____15064 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____15064 with
                | (env0,topt) ->
                    let uu____15083 = build_let_rec_env false env0 lbs1  in
                    (match uu____15083 with
                     | (lbs2,rec_env) ->
                         let uu____15102 = check_let_recs rec_env lbs2  in
                         (match uu____15102 with
                          | (lbs3,g_lbs) ->
                              let uu____15121 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___99_15144 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___99_15144.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___99_15144.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___100_15146 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___100_15146.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___100_15146.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___100_15146.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___100_15146.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___100_15146.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___100_15146.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____15121 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____15173 = tc_term env2 e21  in
                                   (match uu____15173 with
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
                                          let uu____15192 =
                                            let uu____15193 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____15193 g2
                                             in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____15192
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
                                          let uu___101_15197 = cres3  in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___101_15197.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___101_15197.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___101_15197.FStar_Syntax_Syntax.comp_thunk)
                                          }  in
                                        let uu____15198 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____15198 with
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
                                                  uu____15234 ->
                                                  (e, cres4, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  let cres5 =
                                                    let uu___102_15239 =
                                                      cres4  in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___102_15239.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___102_15239.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp_thunk
                                                        =
                                                        (uu___102_15239.FStar_Syntax_Syntax.comp_thunk)
                                                    }  in
                                                  (e, cres5, guard)))))))))
      | uu____15242 -> failwith "Impossible"

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
          let uu____15271 = FStar_Options.ml_ish ()  in
          if uu____15271
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____15274 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____15274 with
             | (formals,c) ->
                 let uu____15299 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____15299 with
                  | (actuals,uu____15309,uu____15310) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____15323 =
                          let uu____15328 =
                            let uu____15329 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____15330 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____15329 uu____15330
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____15328)
                           in
                        FStar_Errors.raise_error uu____15323
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____15333 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____15333 actuals
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
                                (let uu____15354 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____15354)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____15372 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____15372)
                               in
                            let msg =
                              let uu____15380 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____15381 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____15380 uu____15381 formals_msg
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
        let uu____15388 =
          FStar_List.fold_left
            (fun uu____15414  ->
               fun lb  ->
                 match uu____15414 with
                 | (lbs1,env1) ->
                     let uu____15434 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____15434 with
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
                              (let uu____15454 =
                                 let uu____15461 =
                                   let uu____15462 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____15462
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___103_15473 = env0  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___103_15473.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___103_15473.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___103_15473.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___103_15473.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___103_15473.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___103_15473.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___103_15473.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___103_15473.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___103_15473.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___103_15473.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___103_15473.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___103_15473.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___103_15473.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___103_15473.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___103_15473.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___103_15473.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___103_15473.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___103_15473.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___103_15473.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___103_15473.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___103_15473.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___103_15473.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___103_15473.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___103_15473.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___103_15473.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___103_15473.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___103_15473.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___103_15473.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___103_15473.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___103_15473.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___103_15473.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___103_15473.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___103_15473.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___103_15473.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___103_15473.FStar_TypeChecker_Env.dep_graph)
                                    }) t uu____15461
                                  in
                               match uu____15454 with
                               | (t1,uu____15475,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g
                                      in
                                   ((let uu____15479 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1
                                        in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____15479);
                                    norm env0 t1))
                             in
                          let env3 =
                            let uu____15481 =
                              termination_check_enabled
                                lb.FStar_Syntax_Syntax.lbname e t1
                               in
                            if uu____15481
                            then
                              let uu___104_15482 = env2  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___104_15482.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___104_15482.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___104_15482.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___104_15482.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___104_15482.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___104_15482.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___104_15482.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___104_15482.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___104_15482.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___104_15482.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___104_15482.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___104_15482.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1,
                                     univ_vars1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___104_15482.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___104_15482.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___104_15482.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___104_15482.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___104_15482.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___104_15482.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___104_15482.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___104_15482.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___104_15482.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___104_15482.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___104_15482.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___104_15482.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___104_15482.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___104_15482.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___104_15482.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___104_15482.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___104_15482.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.splice =
                                  (uu___104_15482.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___104_15482.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___104_15482.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___104_15482.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___104_15482.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___104_15482.FStar_TypeChecker_Env.dep_graph)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname
                                (univ_vars1, t1)
                             in
                          let lb1 =
                            let uu___105_15499 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___105_15499.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___105_15499.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___105_15499.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___105_15499.FStar_Syntax_Syntax.lbpos)
                            }  in
                          ((lb1 :: lbs1), env3))) ([], env) lbs
           in
        match uu____15388 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lbs  ->
      let uu____15522 =
        let uu____15531 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____15557 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____15557 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____15585 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____15585
                       | uu____15590 ->
                           let lb1 =
                             let uu___106_15593 = lb  in
                             let uu____15594 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___106_15593.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___106_15593.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___106_15593.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___106_15593.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____15594;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___106_15593.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___106_15593.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____15597 =
                             let uu____15604 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____15604
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____15597 with
                            | (e,c,g) ->
                                ((let uu____15613 =
                                    let uu____15614 =
                                      FStar_Syntax_Util.is_total_lcomp c  in
                                    Prims.op_Negation uu____15614  in
                                  if uu____15613
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
        FStar_All.pipe_right uu____15531 FStar_List.unzip  in
      match uu____15522 with
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
        let uu____15663 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____15663 with
        | (env1,uu____15681) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____15689 = check_lbtyp top_level env lb  in
            (match uu____15689 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____15733 =
                     tc_maybe_toplevel_term
                       (let uu___107_15742 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___107_15742.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___107_15742.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___107_15742.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___107_15742.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___107_15742.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___107_15742.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___107_15742.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___107_15742.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___107_15742.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___107_15742.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___107_15742.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___107_15742.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___107_15742.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___107_15742.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___107_15742.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___107_15742.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___107_15742.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___107_15742.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___107_15742.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.failhard =
                            (uu___107_15742.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___107_15742.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___107_15742.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___107_15742.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___107_15742.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___107_15742.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___107_15742.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___107_15742.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___107_15742.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___107_15742.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.splice =
                            (uu___107_15742.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___107_15742.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___107_15742.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___107_15742.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___107_15742.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___107_15742.FStar_TypeChecker_Env.dep_graph)
                        }) e11
                      in
                   match uu____15733 with
                   | (e12,c1,g1) ->
                       let uu____15756 =
                         let uu____15761 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____15765  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____15761 e12 c1 wf_annot
                          in
                       (match uu____15756 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f  in
                            ((let uu____15780 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____15780
                              then
                                let uu____15781 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____15782 =
                                  FStar_Syntax_Print.lcomp_to_string c11  in
                                let uu____15783 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____15781 uu____15782 uu____15783
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
            let uu____15817 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____15817 with
             | (univ_opening,univ_vars1) ->
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                   univ_opening, env))
        | uu____15856 ->
            let uu____15857 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____15857 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____15906 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____15906)
                 else
                   (let uu____15914 = FStar_Syntax_Util.type_u ()  in
                    match uu____15914 with
                    | (k,uu____15934) ->
                        let uu____15935 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____15935 with
                         | (t2,uu____15957,g) ->
                             ((let uu____15960 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____15960
                               then
                                 let uu____15961 =
                                   let uu____15962 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____15962
                                    in
                                 let uu____15963 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____15961 uu____15963
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____15966 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____15966))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun uu____15974  ->
      match uu____15974 with
      | (x,imp) ->
          let uu____15993 = FStar_Syntax_Util.type_u ()  in
          (match uu____15993 with
           | (tu,u) ->
               ((let uu____16013 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____16013
                 then
                   let uu____16014 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____16015 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____16016 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____16014 uu____16015 uu____16016
                 else ());
                (let uu____16018 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____16018 with
                 | (t,uu____16038,g) ->
                     let x1 =
                       ((let uu___108_16046 = x  in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___108_16046.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___108_16046.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp)
                        in
                     ((let uu____16048 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High
                          in
                       if uu____16048
                       then
                         let uu____16049 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1)
                            in
                         let uu____16050 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____16049 uu____16050
                       else ());
                      (let uu____16052 = push_binding env x1  in
                       (x1, uu____16052, g, u))))))

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
            let uu____16142 = tc_binder env1 b  in
            (match uu____16142 with
             | (b1,env',g,u) ->
                 let uu____16183 = aux env' bs2  in
                 (match uu____16183 with
                  | (bs3,env'1,g',us) ->
                      let uu____16236 =
                        let uu____16237 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g'
                           in
                        FStar_TypeChecker_Rel.conj_guard g uu____16237  in
                      ((b1 :: bs3), env'1, uu____16236, (u :: us))))
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
          (fun uu____16322  ->
             fun uu____16323  ->
               match (uu____16322, uu____16323) with
               | ((t,imp),(args1,g)) ->
                   let uu____16392 = tc_term env1 t  in
                   (match uu____16392 with
                    | (t1,uu____16410,g') ->
                        let uu____16412 =
                          FStar_TypeChecker_Rel.conj_guard g g'  in
                        (((t1, imp) :: args1), uu____16412))) args
          ([], FStar_TypeChecker_Rel.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____16454  ->
             match uu____16454 with
             | (pats1,g) ->
                 let uu____16479 = tc_args env p  in
                 (match uu____16479 with
                  | (args,g') ->
                      let uu____16492 = FStar_TypeChecker_Rel.conj_guard g g'
                         in
                      ((args :: pats1), uu____16492))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let uu____16505 = tc_maybe_toplevel_term env e  in
      match uu____16505 with
      | (e1,c,g) ->
          let uu____16521 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c  in
          if uu____16521
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c  in
             let c2 = norm_c env c1  in
             let uu____16532 =
               let uu____16537 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2)
                  in
               if uu____16537
               then
                 let uu____16542 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2)
                    in
                 (uu____16542, false)
               else
                 (let uu____16544 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2)
                     in
                  (uu____16544, true))
                in
             match uu____16532 with
             | (target_comp,allow_ghost) ->
                 let uu____16553 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                 (match uu____16553 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____16563 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp  in
                      let uu____16564 =
                        FStar_TypeChecker_Rel.conj_guard g1 g'  in
                      (e1, uu____16563, uu____16564)
                  | uu____16565 ->
                      if allow_ghost
                      then
                        let uu____16574 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2
                           in
                        FStar_Errors.raise_error uu____16574
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____16586 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2
                            in
                         FStar_Errors.raise_error uu____16586
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
      let uu____16609 = tc_tot_or_gtot_term env t  in
      match uu____16609 with
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
      (let uu____16637 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____16637
       then
         let uu____16638 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____16638
       else ());
      (let env1 =
         let uu___109_16641 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___109_16641.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___109_16641.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___109_16641.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___109_16641.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___109_16641.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___109_16641.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___109_16641.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___109_16641.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___109_16641.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___109_16641.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___109_16641.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___109_16641.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___109_16641.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___109_16641.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___109_16641.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___109_16641.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___109_16641.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___109_16641.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___109_16641.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___109_16641.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___109_16641.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___109_16641.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___109_16641.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___109_16641.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___109_16641.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___109_16641.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___109_16641.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___109_16641.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.splice =
             (uu___109_16641.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___109_16641.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___109_16641.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___109_16641.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___109_16641.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___109_16641.FStar_TypeChecker_Env.dep_graph)
         }  in
       let uu____16648 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (e1,msg,uu____16683) ->
             let uu____16684 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____16684
          in
       match uu____16648 with
       | (t,c,g) ->
           let uu____16700 = FStar_Syntax_Util.is_total_lcomp c  in
           if uu____16700
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____16710 =
                let uu____16715 =
                  let uu____16716 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____16716
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____16715)
                 in
              let uu____16717 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____16710 uu____16717))
  
let level_of_type_fail :
  'Auu____16728 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____16728
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____16741 =
          let uu____16746 =
            let uu____16747 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____16747 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____16746)  in
        let uu____16748 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____16741 uu____16748
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____16765 =
            let uu____16766 = FStar_Syntax_Util.unrefine t1  in
            uu____16766.FStar_Syntax_Syntax.n  in
          match uu____16765 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____16770 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____16773 = FStar_Syntax_Util.type_u ()  in
                 match uu____16773 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___112_16781 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___112_16781.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___112_16781.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___112_16781.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___112_16781.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___112_16781.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___112_16781.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___112_16781.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___112_16781.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___112_16781.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___112_16781.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___112_16781.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___112_16781.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___112_16781.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___112_16781.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___112_16781.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___112_16781.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___112_16781.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___112_16781.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___112_16781.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___112_16781.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___112_16781.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___112_16781.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___112_16781.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___112_16781.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___112_16781.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___112_16781.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___112_16781.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___112_16781.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___112_16781.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.splice =
                           (uu___112_16781.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___112_16781.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___112_16781.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___112_16781.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___112_16781.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___112_16781.FStar_TypeChecker_Env.dep_graph)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____16785 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____16785
                       | uu____16786 ->
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
      let uu____16795 =
        let uu____16796 = FStar_Syntax_Subst.compress e  in
        uu____16796.FStar_Syntax_Syntax.n  in
      match uu____16795 with
      | FStar_Syntax_Syntax.Tm_bvar uu____16801 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____16806 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____16833 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____16849) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____16872,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____16899) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____16906 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____16906 with | ((uu____16917,t),uu____16919) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____16925 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____16925
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16926,(FStar_Util.Inl t,uu____16928),uu____16929) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16976,(FStar_Util.Inr c,uu____16978),uu____16979) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____17029;
             FStar_Syntax_Syntax.vars = uu____17030;_},us)
          ->
          let uu____17036 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____17036 with
           | ((us',t),uu____17049) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____17055 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____17055)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____17071 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____17072 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____17082) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____17105 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____17105 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____17125  ->
                      match uu____17125 with
                      | (b,uu____17131) ->
                          let uu____17132 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____17132) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____17137 = universe_of_aux env res  in
                 level_of_type env res uu____17137  in
               let u_c =
                 let uu____17139 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res  in
                 match uu____17139 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____17143 = universe_of_aux env trepr  in
                     level_of_type env trepr uu____17143
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
            | FStar_Syntax_Syntax.Tm_bvar uu____17236 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____17251 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____17290 ->
                let uu____17291 = universe_of_aux env hd3  in
                (uu____17291, args1)
            | FStar_Syntax_Syntax.Tm_name uu____17304 ->
                let uu____17305 = universe_of_aux env hd3  in
                (uu____17305, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____17318 ->
                let uu____17335 = universe_of_aux env hd3  in
                (uu____17335, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____17348 ->
                let uu____17355 = universe_of_aux env hd3  in
                (uu____17355, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____17368 ->
                let uu____17395 = universe_of_aux env hd3  in
                (uu____17395, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____17408 ->
                let uu____17415 = universe_of_aux env hd3  in
                (uu____17415, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____17428 ->
                let uu____17429 = universe_of_aux env hd3  in
                (uu____17429, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____17442 ->
                let uu____17455 = universe_of_aux env hd3  in
                (uu____17455, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____17468 ->
                let uu____17475 = universe_of_aux env hd3  in
                (uu____17475, args1)
            | FStar_Syntax_Syntax.Tm_type uu____17488 ->
                let uu____17489 = universe_of_aux env hd3  in
                (uu____17489, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____17502,hd4::uu____17504) ->
                let uu____17569 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____17569 with
                 | (uu____17584,uu____17585,hd5) ->
                     let uu____17603 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____17603 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____17654 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e
                   in
                let uu____17656 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____17656 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____17707 ->
                let uu____17708 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____17708 with
                 | (env1,uu____17730) ->
                     let env2 =
                       let uu___113_17736 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___113_17736.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___113_17736.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___113_17736.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___113_17736.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___113_17736.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___113_17736.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___113_17736.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___113_17736.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___113_17736.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___113_17736.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___113_17736.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___113_17736.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___113_17736.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___113_17736.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___113_17736.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___113_17736.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___113_17736.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___113_17736.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___113_17736.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___113_17736.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___113_17736.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___113_17736.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___113_17736.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___113_17736.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___113_17736.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___113_17736.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___113_17736.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.splice =
                           (uu___113_17736.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___113_17736.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___113_17736.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___113_17736.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___113_17736.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___113_17736.FStar_TypeChecker_Env.dep_graph)
                       }  in
                     ((let uu____17738 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____17738
                       then
                         let uu____17739 =
                           let uu____17740 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____17740  in
                         let uu____17741 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____17739 uu____17741
                       else ());
                      (let uu____17743 = tc_term env2 hd3  in
                       match uu____17743 with
                       | (uu____17764,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____17765;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____17767;
                                        FStar_Syntax_Syntax.comp_thunk =
                                          uu____17768;_},g)
                           ->
                           ((let uu____17787 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____17787
                               FStar_Pervasives.ignore);
                            (t, args1)))))
             in
          let uu____17798 = type_of_head true hd1 args  in
          (match uu____17798 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t
                  in
               let uu____17838 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____17838 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____17882 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____17882)))
      | FStar_Syntax_Syntax.Tm_match (uu____17885,hd1::uu____17887) ->
          let uu____17952 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____17952 with
           | (uu____17955,uu____17956,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____17974,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____18017 = universe_of_aux env e  in
      level_of_type env e uu____18017
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun tps  ->
      let uu____18036 = tc_binders env tps  in
      match uu____18036 with
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
      let uu____18080 =
        let uu____18081 = FStar_Syntax_Subst.compress t  in
        uu____18081.FStar_Syntax_Syntax.n  in
      match uu____18080 with
      | FStar_Syntax_Syntax.Tm_delayed uu____18086 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____18113 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____18120 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____18120
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____18122 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____18122
            (fun uu____18136  ->
               match uu____18136 with
               | (t1,uu____18144) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____18146;
             FStar_Syntax_Syntax.vars = uu____18147;_},us)
          ->
          let uu____18153 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____18153
            (fun uu____18167  ->
               match uu____18167 with
               | (t1,uu____18175) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____18177 = tc_constant env t.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____18177
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____18179 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____18179
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____18188;_})
          ->
          let mk_comp =
            if FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              if
                FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid
              then
                FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
              else FStar_Pervasives_Native.None
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____18275 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____18275
                 (fun u  ->
                    let uu____18283 =
                      let uu____18286 =
                        let uu____18289 =
                          let uu____18290 =
                            let uu____18303 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____18303)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____18290  in
                        FStar_Syntax_Syntax.mk uu____18289  in
                      uu____18286 FStar_Pervasives_Native.None
                        t.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____18283))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____18333 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____18333 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____18380 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____18380
                       (fun uc  ->
                          let uu____18388 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____18388)
                 | (x,imp)::bs3 ->
                     let uu____18406 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____18406
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____18415 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____18433) ->
          let uu____18438 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____18438
            (fun u_x  ->
               let uu____18446 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____18446)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____18482 =
              let uu____18483 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____18483.FStar_Syntax_Syntax.n  in
            match uu____18482 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____18545 = FStar_Util.first_N n_args bs  in
                    match uu____18545 with
                    | (bs1,rest) ->
                        let t1 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____18615 =
                          let uu____18620 = FStar_Syntax_Syntax.mk_Total t1
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____18620  in
                        (match uu____18615 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____18656 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____18656 with
                       | (bs1,c1) ->
                           let uu____18671 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____18671
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____18713  ->
                     match uu____18713 with
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
                         let uu____18759 = FStar_Syntax_Subst.subst subst1 t1
                            in
                         FStar_Pervasives_Native.Some uu____18759)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____18761) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____18767,uu____18768) ->
                aux t1
            | uu____18809 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____18810,(FStar_Util.Inl t1,uu____18812),uu____18813) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____18862,(FStar_Util.Inr c,uu____18864),uu____18865) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (uu____18914,t1) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____18943) ->
          type_of_well_typed_term env t1
      | FStar_Syntax_Syntax.Tm_match uu____18948 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____18971 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____18984 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____18995 = type_of_well_typed_term env t  in
      match uu____18995 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____19001;
            FStar_Syntax_Syntax.vars = uu____19002;_}
          -> FStar_Pervasives_Native.Some u
      | uu____19007 -> FStar_Pervasives_Native.None

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
            let uu___114_19024 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___114_19024.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___114_19024.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___114_19024.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___114_19024.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___114_19024.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___114_19024.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___114_19024.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___114_19024.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___114_19024.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___114_19024.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___114_19024.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___114_19024.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___114_19024.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___114_19024.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___114_19024.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___114_19024.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___114_19024.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___114_19024.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___114_19024.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___114_19024.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___114_19024.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___114_19024.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___114_19024.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___114_19024.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___114_19024.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___114_19024.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___114_19024.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___114_19024.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___114_19024.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.splice =
                (uu___114_19024.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___114_19024.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___114_19024.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___114_19024.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___114_19024.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___114_19024.FStar_TypeChecker_Env.dep_graph)
            }  in
          let slow_check uu____19028 =
            if must_total
            then
              let uu____19029 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____19029 with | (uu____19036,uu____19037,g) -> g
            else
              (let uu____19040 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____19040 with | (uu____19047,uu____19048,g) -> g)
             in
          let uu____19050 =
            let uu____19051 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____19051  in
          if uu____19050
          then slow_check ()
          else
            (let uu____19053 = type_of_well_typed_term env2 t  in
             match uu____19053 with
             | FStar_Pervasives_Native.None  -> slow_check ()
             | FStar_Pervasives_Native.Some k' ->
                 ((let uu____19058 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                       (FStar_Options.Other "FastImplicits")
                      in
                   if uu____19058
                   then
                     let uu____19059 =
                       FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                        in
                     let uu____19060 = FStar_Syntax_Print.term_to_string t
                        in
                     let uu____19061 = FStar_Syntax_Print.term_to_string k'
                        in
                     let uu____19062 = FStar_Syntax_Print.term_to_string k
                        in
                     FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                       uu____19059 uu____19060 uu____19061 uu____19062
                   else ());
                  (let b = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                   (let uu____19066 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                        (FStar_Options.Other "FastImplicits")
                       in
                    if uu____19066
                    then
                      let uu____19067 =
                        FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                         in
                      let uu____19068 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____19069 = FStar_Syntax_Print.term_to_string k'
                         in
                      let uu____19070 = FStar_Syntax_Print.term_to_string k
                         in
                      FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                        uu____19067 (if b then "succeeded" else "failed")
                        uu____19068 uu____19069 uu____19070
                    else ());
                   if b
                   then FStar_TypeChecker_Rel.trivial_guard
                   else slow_check ())))
  