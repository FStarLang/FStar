open Prims
let instantiate_both: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___64_4 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___64_4.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___64_4.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___64_4.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___64_4.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___64_4.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___64_4.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___64_4.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___64_4.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___64_4.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___64_4.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___64_4.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___64_4.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___64_4.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___64_4.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___64_4.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___64_4.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___64_4.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___64_4.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___64_4.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___64_4.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___64_4.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___64_4.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___64_4.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___64_4.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___64_4.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___64_4.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___64_4.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___64_4.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___64_4.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___64_4.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___64_4.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___64_4.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___64_4.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___64_4.FStar_TypeChecker_Env.dep_graph)
    }
let no_inst: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___65_8 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___65_8.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___65_8.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___65_8.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___65_8.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___65_8.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___65_8.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___65_8.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___65_8.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___65_8.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___65_8.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___65_8.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___65_8.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___65_8.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___65_8.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___65_8.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___65_8.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___65_8.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___65_8.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___65_8.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___65_8.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___65_8.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___65_8.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___65_8.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___65_8.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___65_8.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___65_8.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___65_8.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___65_8.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___65_8.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___65_8.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___65_8.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___65_8.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___65_8.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___65_8.FStar_TypeChecker_Env.dep_graph)
    }
let mk_lex_list:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
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
                 tl1.FStar_Syntax_Syntax.pos in
           let uu____40 =
             let uu____41 =
               let uu____42 = FStar_Syntax_Syntax.as_arg v1 in
               let uu____43 =
                 let uu____46 = FStar_Syntax_Syntax.as_arg tl1 in [uu____46] in
               uu____42 :: uu____43 in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____41 in
           uu____40 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
let is_eq:
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___59_53  ->
    match uu___59_53 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____56 -> false
let steps:
  'Auu____61 . 'Auu____61 -> FStar_TypeChecker_Normalize.step Prims.list =
  fun env  ->
    [FStar_TypeChecker_Normalize.Beta;
    FStar_TypeChecker_Normalize.Eager_unfolding]
let norm:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> FStar_TypeChecker_Normalize.normalize (steps env) env t
let norm_c:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  -> FStar_TypeChecker_Normalize.normalize_comp (steps env) env c
let check_no_escape:
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.bv Prims.list ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun head_opt  ->
    fun env  ->
      fun fvs  ->
        fun kt  ->
          let rec aux try_norm t =
            match fvs with
            | [] -> t
            | uu____107 ->
                let t1 = if try_norm then norm env t else t in
                let fvs' = FStar_Syntax_Free.names t1 in
                let uu____115 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs in
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
                                  FStar_Syntax_Print.bv_to_string x in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____127
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____129 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____130 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1 in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____129 uu____130 in
                          let uu____131 = FStar_TypeChecker_Env.get_range env in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____131 in
                        let s =
                          let uu____133 =
                            let uu____134 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____134 in
                          FStar_TypeChecker_Util.new_uvar env uu____133 in
                        let uu____143 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s in
                        match uu____143 with
                        | FStar_Pervasives_Native.Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____148 -> fail ())) in
          aux false kt
let push_binding:
  'Auu____154 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____154) FStar_Pervasives_Native.tuple2 ->
        FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun b  ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
let maybe_extend_subst:
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.binder ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t
  =
  fun s  ->
    fun b  ->
      fun v1  ->
        let uu____184 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____184
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v1))
          :: s
let set_lcomp_result:
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____196  ->
           let uu____197 = FStar_Syntax_Syntax.lcomp_comp lc in
           FStar_Syntax_Util.set_result_typ uu____197 t)
let memo_tk:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  = fun e  -> fun t  -> e
let value_check_expected_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.lcomp) FStar_Util.either
        ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun tlc  ->
        fun guard  ->
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____240 = FStar_Syntax_Syntax.mk_Total t in
                FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____240
            | FStar_Util.Inr lc -> lc in
          let t = lc.FStar_Syntax_Syntax.res_typ in
          let uu____249 =
            let uu____256 = FStar_TypeChecker_Env.expected_typ env in
            match uu____256 with
            | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                let uu____266 =
                  FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                    t' in
                (match uu____266 with
                 | (e1,lc1) ->
                     let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                     let uu____282 =
                       FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                     (match uu____282 with
                      | (e2,g) ->
                          ((let uu____296 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High in
                            if uu____296
                            then
                              let uu____297 =
                                FStar_Syntax_Print.term_to_string t1 in
                              let uu____298 =
                                FStar_Syntax_Print.term_to_string t' in
                              let uu____299 =
                                FStar_TypeChecker_Rel.guard_to_string env g in
                              let uu____300 =
                                FStar_TypeChecker_Rel.guard_to_string env
                                  guard in
                              FStar_Util.print4
                                "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                uu____297 uu____298 uu____299 uu____300
                            else ());
                           (let msg =
                              let uu____307 =
                                FStar_TypeChecker_Rel.is_trivial g in
                              if uu____307
                              then FStar_Pervasives_Native.None
                              else
                                FStar_All.pipe_left
                                  (fun _0_40  ->
                                     FStar_Pervasives_Native.Some _0_40)
                                  (FStar_TypeChecker_Err.subtyping_failed env
                                     t1 t') in
                            let g1 = FStar_TypeChecker_Rel.conj_guard g guard in
                            let uu____324 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                msg env e2 lc1 g1 in
                            match uu____324 with
                            | (lc2,g2) ->
                                let uu____337 = set_lcomp_result lc2 t' in
                                ((memo_tk e2 t'), uu____337, g2))))) in
          match uu____249 with | (e1,lc1,g) -> (e1, lc1, g)
let comp_check_expected_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let uu____368 = FStar_TypeChecker_Env.expected_typ env in
        match uu____368 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____378 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____378 with
             | (e1,lc1) ->
                 FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
let check_expected_effect:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun copt  ->
      fun uu____411  ->
        match uu____411 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____440 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____440
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____442 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____442
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____444 =
              match copt with
              | FStar_Pervasives_Native.Some uu____457 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____460 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____462 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____462)) in
                  if uu____460
                  then
                    let uu____469 =
                      let uu____472 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos in
                      FStar_Pervasives_Native.Some uu____472 in
                    (uu____469, c)
                  else
                    (let uu____476 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____476
                     then
                       let uu____483 = tot_or_gtot c in
                       (FStar_Pervasives_Native.None, uu____483)
                     else
                       (let uu____487 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____487
                        then
                          let uu____494 =
                            let uu____497 = tot_or_gtot c in
                            FStar_Pervasives_Native.Some uu____497 in
                          (uu____494, c)
                        else (FStar_Pervasives_Native.None, c))) in
            (match uu____444 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let c3 =
                        let uu____524 = FStar_Syntax_Util.lcomp_of_comp c2 in
                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                          env e uu____524 in
                      let c4 = FStar_Syntax_Syntax.lcomp_comp c3 in
                      let uu____526 =
                        FStar_TypeChecker_Util.check_comp env e c4 expected_c in
                      (match uu____526 with
                       | (e1,uu____540,g) ->
                           let g1 =
                             let uu____543 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_TypeChecker_Util.label_guard uu____543
                               "could not prove post-condition" g in
                           ((let uu____545 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low in
                             if uu____545
                             then
                               let uu____546 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos in
                               let uu____547 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1 in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____546 uu____547
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c4)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c4) in
                             (e2, expected_c, g1))))))
let no_logical_guard:
  'Auu____554 'Auu____555 .
    FStar_TypeChecker_Env.env ->
      ('Auu____555,'Auu____554,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____555,'Auu____554,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____575  ->
      match uu____575 with
      | (te,kt,f) ->
          let uu____585 = FStar_TypeChecker_Rel.guard_form f in
          (match uu____585 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____593 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1 in
               let uu____598 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____593 uu____598)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____608 = FStar_TypeChecker_Env.expected_typ env in
    match uu____608 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____612 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____612
let rec get_pat_vars:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun pats  ->
    fun acc  ->
      let pats1 = FStar_Syntax_Util.unmeta pats in
      let uu____636 = FStar_Syntax_Util.head_and_args pats1 in
      match uu____636 with
      | (head1,args) ->
          let uu____675 =
            let uu____676 = FStar_Syntax_Util.un_uinst head1 in
            uu____676.FStar_Syntax_Syntax.n in
          (match uu____675 with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid
               ->
               let uu____683 = FStar_List.tl args in
               get_pat_vars_args uu____683 acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.smtpatOr_lid
               -> get_pat_vars_args args acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               -> get_pat_vars_args args acc
           | uu____692 ->
               let uu____693 = FStar_Syntax_Free.names pats1 in
               FStar_Util.set_union acc uu____693)
and get_pat_vars_args:
  FStar_Syntax_Syntax.args ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun args  ->
    fun acc  ->
      FStar_List.fold_left
        (fun s  ->
           fun arg  -> get_pat_vars (FStar_Pervasives_Native.fst arg) s) acc
        args
let check_smt_pat:
  'Auu____723 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,'Auu____723) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____756 = FStar_Syntax_Util.is_smt_lemma t in
          if uu____756
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____757;
                  FStar_Syntax_Syntax.effect_name = uu____758;
                  FStar_Syntax_Syntax.result_typ = uu____759;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____763)::[];
                  FStar_Syntax_Syntax.flags = uu____764;_}
                ->
                let pat_vars =
                  let uu____812 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta] env pats in
                  let uu____813 =
                    FStar_Util.new_set FStar_Syntax_Syntax.order_bv in
                  get_pat_vars uu____812 uu____813 in
                let uu____816 =
                  FStar_All.pipe_right bs
                    (FStar_Util.find_opt
                       (fun uu____843  ->
                          match uu____843 with
                          | (b,uu____849) ->
                              let uu____850 = FStar_Util.set_mem b pat_vars in
                              Prims.op_Negation uu____850)) in
                (match uu____816 with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some (x,uu____856) ->
                     let uu____861 =
                       let uu____866 =
                         let uu____867 = FStar_Syntax_Print.bv_to_string x in
                         FStar_Util.format1
                           "Pattern misses at least one bound variable: %s"
                           uu____867 in
                       (FStar_Errors.Warning_PatternMissingBoundVar,
                         uu____866) in
                     FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       uu____861)
            | uu____868 -> failwith "Impossible"
          else ()
let guard_letrecs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
          FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        match env.FStar_TypeChecker_Env.letrecs with
        | [] -> []
        | letrecs ->
            let r = FStar_TypeChecker_Env.get_range env in
            let env1 =
              let uu___66_918 = env in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___66_918.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___66_918.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___66_918.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___66_918.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___66_918.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___66_918.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___66_918.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___66_918.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___66_918.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___66_918.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___66_918.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___66_918.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___66_918.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___66_918.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___66_918.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___66_918.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___66_918.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___66_918.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___66_918.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.failhard =
                  (uu___66_918.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___66_918.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.tc_term =
                  (uu___66_918.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___66_918.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___66_918.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___66_918.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___66_918.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qname_and_index =
                  (uu___66_918.FStar_TypeChecker_Env.qname_and_index);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___66_918.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth =
                  (uu___66_918.FStar_TypeChecker_Env.synth);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___66_918.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___66_918.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___66_918.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___66_918.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___66_918.FStar_TypeChecker_Env.dep_graph)
              } in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid in
            let decreases_clause bs c =
              (let uu____934 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
               if uu____934
               then
                 let uu____935 = FStar_Syntax_Print.binders_to_string ", " bs in
                 let uu____936 = FStar_Syntax_Print.comp_to_string c in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n" uu____935
                   uu____936
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____955  ->
                         match uu____955 with
                         | (b,uu____963) ->
                             let t =
                               let uu____965 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____965 in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____968 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____969 -> []
                              | uu____982 ->
                                  let uu____983 =
                                    FStar_Syntax_Syntax.bv_to_name b in
                                  [uu____983]))) in
               let as_lex_list dec =
                 let uu____988 = FStar_Syntax_Util.head_and_args dec in
                 match uu____988 with
                 | (head1,uu____1004) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____1026 -> mk_lex_list [dec]) in
               let cflags = FStar_Syntax_Util.comp_flags c in
               let uu____1030 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___60_1039  ->
                         match uu___60_1039 with
                         | FStar_Syntax_Syntax.DECREASES uu____1040 -> true
                         | uu____1043 -> false)) in
               match uu____1030 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____1047 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions in
                   (match xs with | x::[] -> x | uu____1056 -> mk_lex_list xs)) in
            let previous_dec = decreases_clause actuals expected_c in
            let guard_one_letrec uu____1077 =
              match uu____1077 with
              | (l,t,u_names) ->
                  let uu____1095 =
                    let uu____1096 = FStar_Syntax_Subst.compress t in
                    uu____1096.FStar_Syntax_Syntax.n in
                  (match uu____1095 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____1157  ->
                                 match uu____1157 with
                                 | (x,imp) ->
                                     let uu____1168 =
                                       FStar_Syntax_Syntax.is_null_bv x in
                                     if uu____1168
                                     then
                                       let uu____1173 =
                                         let uu____1174 =
                                           let uu____1177 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x in
                                           FStar_Pervasives_Native.Some
                                             uu____1177 in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____1174
                                           x.FStar_Syntax_Syntax.sort in
                                       (uu____1173, imp)
                                     else (x, imp))) in
                       let uu____1179 =
                         FStar_Syntax_Subst.open_comp formals1 c in
                       (match uu____1179 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1 in
                            let precedes1 =
                              let uu____1198 =
                                let uu____1199 =
                                  let uu____1200 =
                                    FStar_Syntax_Syntax.as_arg dec in
                                  let uu____1201 =
                                    let uu____1204 =
                                      FStar_Syntax_Syntax.as_arg previous_dec in
                                    [uu____1204] in
                                  uu____1200 :: uu____1201 in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____1199 in
                              uu____1198 FStar_Pervasives_Native.None r in
                            let uu____1207 = FStar_Util.prefix formals2 in
                            (match uu____1207 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___67_1254 = last1 in
                                   let uu____1255 =
                                     FStar_Syntax_Util.refine last1 precedes1 in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___67_1254.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___67_1254.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____1255
                                   } in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)] in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1 in
                                 ((let uu____1281 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low in
                                   if uu____1281
                                   then
                                     let uu____1282 =
                                       FStar_Syntax_Print.lbname_to_string l in
                                     let uu____1283 =
                                       FStar_Syntax_Print.term_to_string t in
                                     let uu____1284 =
                                       FStar_Syntax_Print.term_to_string t' in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____1282 uu____1283 uu____1284
                                   else ());
                                  (l, t', u_names))))
                   | uu____1288 ->
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_ExpectedArrowAnnotatedType,
                           "Annotated type of 'let rec' must be an arrow")
                         t.FStar_Syntax_Syntax.pos) in
            FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec)
let rec tc_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      tc_maybe_toplevel_term
        (let uu___68_1739 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___68_1739.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___68_1739.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___68_1739.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___68_1739.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___68_1739.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___68_1739.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___68_1739.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___68_1739.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___68_1739.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___68_1739.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___68_1739.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___68_1739.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___68_1739.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___68_1739.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___68_1739.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___68_1739.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___68_1739.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___68_1739.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___68_1739.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___68_1739.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___68_1739.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___68_1739.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___68_1739.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___68_1739.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___68_1739.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___68_1739.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___68_1739.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___68_1739.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___68_1739.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___68_1739.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___68_1739.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___68_1739.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___68_1739.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___68_1739.FStar_TypeChecker_Env.dep_graph)
         }) e
and tc_maybe_toplevel_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      (let uu____1751 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1751
       then
         let uu____1752 =
           let uu____1753 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1753 in
         let uu____1754 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1752 uu____1754
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1763 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1794 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1801 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1818 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1819 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1820 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1821 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1822 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1839 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1852 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1859 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____1860;
              FStar_Syntax_Syntax.vars = uu____1861;_},FStar_Syntax_Syntax.Meta_alien
            (uu____1862,uu____1863,ty))
           ->
           let uu____1873 =
             let uu____1874 = FStar_Syntax_Syntax.mk_Total ty in
             FStar_All.pipe_right uu____1874 FStar_Syntax_Util.lcomp_of_comp in
           (top, uu____1873, FStar_TypeChecker_Rel.trivial_guard)
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1880 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1880 with
            | (e2,c,g) ->
                let g1 =
                  let uu___69_1897 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___69_1897.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___69_1897.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___69_1897.FStar_TypeChecker_Env.implicits)
                  } in
                let uu____1898 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (uu____1898, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1919 = FStar_Syntax_Util.type_u () in
           (match uu____1919 with
            | (t,u) ->
                let uu____1932 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1932 with
                 | (e2,c,g) ->
                     let uu____1948 =
                       let uu____1963 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____1963 with
                       | (env2,uu____1985) -> tc_pats env2 pats in
                     (match uu____1948 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___70_2019 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___70_2019.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___70_2019.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___70_2019.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____2020 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____2023 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____2020, c, uu____2023))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____2031 =
             let uu____2032 = FStar_Syntax_Subst.compress e1 in
             uu____2032.FStar_Syntax_Syntax.n in
           (match uu____2031 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____2041,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____2043;
                               FStar_Syntax_Syntax.lbtyp = uu____2044;
                               FStar_Syntax_Syntax.lbeff = uu____2045;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____2070 =
                  let uu____2077 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit in
                  tc_term uu____2077 e11 in
                (match uu____2070 with
                 | (e12,c1,g1) ->
                     let uu____2087 = tc_term env1 e2 in
                     (match uu____2087 with
                      | (e21,c2,g2) ->
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
                            let uu____2111 =
                              let uu____2114 =
                                let uu____2115 =
                                  let uu____2128 =
                                    let uu____2135 =
                                      let uu____2138 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13) in
                                      [uu____2138] in
                                    (false, uu____2135) in
                                  (uu____2128, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____2115 in
                              FStar_Syntax_Syntax.mk uu____2114 in
                            uu____2111 FStar_Pervasives_Native.None
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
                          let uu____2160 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____2160)))
            | uu____2163 ->
                let uu____2164 = tc_term env1 e1 in
                (match uu____2164 with
                 | (e2,c,g) ->
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2186) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____2198) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____2217 = tc_term env1 e1 in
           (match uu____2217 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____2241) ->
           let uu____2288 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2288 with
            | (env0,uu____2302) ->
                let uu____2307 = tc_comp env0 expected_c in
                (match uu____2307 with
                 | (expected_c1,uu____2321,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____2326 =
                       let uu____2333 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____2333 e1 in
                     (match uu____2326 with
                      | (e2,c',g') ->
                          let uu____2343 =
                            let uu____2350 =
                              let uu____2355 =
                                FStar_Syntax_Syntax.lcomp_comp c' in
                              (e2, uu____2355) in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____2350 in
                          (match uu____2343 with
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
                                   top.FStar_Syntax_Syntax.pos in
                               let lc =
                                 FStar_Syntax_Util.lcomp_of_comp expected_c2 in
                               let f =
                                 let uu____2400 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____2400 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____2409 =
                                            FStar_Syntax_Util.mk_squash
                                              FStar_Syntax_Syntax.U_zero f1 in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____2409) in
                               let uu____2410 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____2410 with
                                | (e5,c,f2) ->
                                    let final_guard =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, final_guard))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____2430) ->
           let uu____2477 = FStar_Syntax_Util.type_u () in
           (match uu____2477 with
            | (k,u) ->
                let uu____2490 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____2490 with
                 | (t1,uu____2504,f) ->
                     let uu____2506 =
                       let uu____2513 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____2513 e1 in
                     (match uu____2506 with
                      | (e2,c,g) ->
                          let uu____2523 =
                            let uu____2528 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____2532  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____2528 e2 c f in
                          (match uu____2523 with
                           | (c1,f1) ->
                               let uu____2541 =
                                 let uu____2548 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2,
                                          ((FStar_Util.Inl t1),
                                            FStar_Pervasives_Native.None),
                                          (FStar_Pervasives_Native.Some
                                             (c1.FStar_Syntax_Syntax.eff_name))))
                                     FStar_Pervasives_Native.None
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____2548 c1 in
                               (match uu____2541 with
                                | (e3,c2,f2) ->
                                    let uu____2588 =
                                      let uu____2589 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____2589 in
                                    (e3, c2, uu____2588))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____2590;
              FStar_Syntax_Syntax.vars = uu____2591;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2654 = FStar_Syntax_Util.head_and_args top in
           (match uu____2654 with
            | (unary_op,uu____2676) ->
                let head1 =
                  let uu____2700 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2700 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____2738;
              FStar_Syntax_Syntax.vars = uu____2739;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2802 = FStar_Syntax_Util.head_and_args top in
           (match uu____2802 with
            | (unary_op,uu____2824) ->
                let head1 =
                  let uu____2848 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2848 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____2886);
              FStar_Syntax_Syntax.pos = uu____2887;
              FStar_Syntax_Syntax.vars = uu____2888;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2951 = FStar_Syntax_Util.head_and_args top in
           (match uu____2951 with
            | (unary_op,uu____2973) ->
                let head1 =
                  let uu____2997 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2997 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3035;
              FStar_Syntax_Syntax.vars = uu____3036;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____3112 = FStar_Syntax_Util.head_and_args top in
           (match uu____3112 with
            | (unary_op,uu____3134) ->
                let head1 =
                  let uu____3158 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____3158 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3202;
              FStar_Syntax_Syntax.vars = uu____3203;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____3241 =
             let uu____3248 =
               let uu____3249 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3249 in
             tc_term uu____3248 e1 in
           (match uu____3241 with
            | (e2,c,g) ->
                let uu____3273 = FStar_Syntax_Util.head_and_args top in
                (match uu____3273 with
                 | (head1,uu____3295) ->
                     let uu____3316 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos in
                     let uu____3343 =
                       let uu____3344 =
                         let uu____3347 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid in
                         FStar_Syntax_Syntax.mk_Total uu____3347 in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____3344 in
                     (uu____3316, uu____3343, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3352;
              FStar_Syntax_Syntax.vars = uu____3353;_},(a1,FStar_Pervasives_Native.None
                                                        )::(a2,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____3406 = FStar_Syntax_Util.head_and_args top in
           (match uu____3406 with
            | (head1,uu____3428) ->
                let env' =
                  let uu____3450 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____3450 in
                let uu____3451 = tc_term env' a1 in
                (match uu____3451 with
                 | (e1,uu____3465,g1) ->
                     let uu____3467 = tc_term env1 a2 in
                     (match uu____3467 with
                      | (e2,t2,g2) ->
                          let g = FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          let uu____3484 =
                            let uu____3487 =
                              let uu____3488 =
                                let uu____3489 =
                                  FStar_Syntax_Syntax.as_arg a1 in
                                let uu____3490 =
                                  let uu____3493 =
                                    FStar_Syntax_Syntax.as_arg a2 in
                                  [uu____3493] in
                                uu____3489 :: uu____3490 in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____3488 in
                            uu____3487 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          (uu____3484, t2, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3498;
              FStar_Syntax_Syntax.vars = uu____3499;_},uu____3500)
           ->
           let uu____3521 =
             let uu____3526 =
               let uu____3527 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.format1 "Ill-applied constant %s" uu____3527 in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____3526) in
           FStar_Errors.raise_error uu____3521 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3534;
              FStar_Syntax_Syntax.vars = uu____3535;_},uu____3536)
           ->
           let uu____3557 =
             let uu____3562 =
               let uu____3563 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.format1 "Ill-applied constant %s" uu____3563 in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____3562) in
           FStar_Errors.raise_error uu____3557 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____3570;
              FStar_Syntax_Syntax.vars = uu____3571;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____3604 = FStar_TypeChecker_Env.clear_expected_typ env1 in
             match uu____3604 with
             | (env0,uu____3618) ->
                 let uu____3623 = tc_term env0 e1 in
                 (match uu____3623 with
                  | (e2,c,g) ->
                      let uu____3639 = FStar_Syntax_Util.head_and_args top in
                      (match uu____3639 with
                       | (reify_op,uu____3661) ->
                           let u_c =
                             let uu____3683 =
                               tc_term env0 c.FStar_Syntax_Syntax.res_typ in
                             match uu____3683 with
                             | (uu____3690,c',uu____3692) ->
                                 let uu____3693 =
                                   let uu____3694 =
                                     FStar_Syntax_Subst.compress
                                       c'.FStar_Syntax_Syntax.res_typ in
                                   uu____3694.FStar_Syntax_Syntax.n in
                                 (match uu____3693 with
                                  | FStar_Syntax_Syntax.Tm_type u -> u
                                  | uu____3698 ->
                                      let uu____3699 =
                                        FStar_Syntax_Util.type_u () in
                                      (match uu____3699 with
                                       | (t,u) ->
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
                                                 let uu____3711 =
                                                   let uu____3712 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       c' in
                                                   let uu____3713 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c.FStar_Syntax_Syntax.res_typ in
                                                   let uu____3714 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c'.FStar_Syntax_Syntax.res_typ in
                                                   FStar_Util.format3
                                                     "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                     uu____3712 uu____3713
                                                     uu____3714 in
                                                 failwith uu____3711);
                                            u))) in
                           let repr =
                             let uu____3716 =
                               FStar_Syntax_Syntax.lcomp_comp c in
                             FStar_TypeChecker_Env.reify_comp env1 uu____3716
                               u_c in
                           let e3 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app
                                  (reify_op, [(e2, aqual)]))
                               FStar_Pervasives_Native.None
                               top.FStar_Syntax_Syntax.pos in
                           let c1 =
                             let uu____3737 =
                               FStar_Syntax_Syntax.mk_Total repr in
                             FStar_All.pipe_right uu____3737
                               FStar_Syntax_Util.lcomp_of_comp in
                           let uu____3738 =
                             comp_check_expected_typ env1 e3 c1 in
                           (match uu____3738 with
                            | (e4,c2,g') ->
                                let uu____3754 =
                                  FStar_TypeChecker_Rel.conj_guard g g' in
                                (e4, c2, uu____3754))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____3756;
              FStar_Syntax_Syntax.vars = uu____3757;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let no_reflect uu____3799 =
               let uu____3800 =
                 let uu____3805 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____3805) in
               FStar_Errors.raise_error uu____3800 e1.FStar_Syntax_Syntax.pos in
             let uu____3812 = FStar_Syntax_Util.head_and_args top in
             match uu____3812 with
             | (reflect_op,uu____3834) ->
                 let uu____3855 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____3855 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____3888 =
                        let uu____3889 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____3889 in
                      if uu____3888
                      then no_reflect ()
                      else
                        (let uu____3899 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____3899 with
                         | (env_no_ex,topt) ->
                             let uu____3918 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____3938 =
                                   let uu____3941 =
                                     let uu____3942 =
                                       let uu____3957 =
                                         let uu____3960 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____3961 =
                                           let uu____3964 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____3964] in
                                         uu____3960 :: uu____3961 in
                                       (repr, uu____3957) in
                                     FStar_Syntax_Syntax.Tm_app uu____3942 in
                                   FStar_Syntax_Syntax.mk uu____3941 in
                                 uu____3938 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos in
                               let uu____3970 =
                                 let uu____3977 =
                                   let uu____3978 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____3978
                                     FStar_Pervasives_Native.fst in
                                 tc_tot_or_gtot_term uu____3977 t in
                               match uu____3970 with
                               | (t1,uu____4006,g) ->
                                   let uu____4008 =
                                     let uu____4009 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____4009.FStar_Syntax_Syntax.n in
                                   (match uu____4008 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____4024,(res,uu____4026)::
                                         (wp,uu____4028)::[])
                                        -> (t1, res, wp, g)
                                    | uu____4071 -> failwith "Impossible") in
                             (match uu____3918 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____4102 =
                                    let uu____4107 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____4107 with
                                    | (e2,c,g) ->
                                        ((let uu____4122 =
                                            let uu____4123 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____4123 in
                                          if uu____4122
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [(FStar_Errors.Error_UnexpectedGTotComputation,
                                                 "Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____4137 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____4137 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____4145 =
                                                  let uu____4154 =
                                                    let uu____4161 =
                                                      let uu____4162 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____4163 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____4162 uu____4163 in
                                                    (FStar_Errors.Error_UnexpectedInstance,
                                                      uu____4161,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____4154] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____4145);
                                               (let uu____4176 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____4176)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____4178 =
                                                let uu____4179 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____4179 in
                                              (e2, uu____4178))) in
                                  (match uu____4102 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____4189 =
                                           let uu____4190 =
                                             let uu____4191 =
                                               let uu____4192 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____4192] in
                                             let uu____4193 =
                                               let uu____4202 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____4202] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____4191;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____4193;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____4190 in
                                         FStar_All.pipe_right uu____4189
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____4222 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____4222 with
                                        | (e4,c1,g') ->
                                            let uu____4238 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____4238))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____4285 =
               let uu____4286 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____4286 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____4285 instantiate_both in
           ((let uu____4302 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____4302
             then
               let uu____4303 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____4304 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____4303
                 uu____4304
             else ());
            (let isquote =
               let uu____4307 = FStar_Syntax_Util.head_and_args head1 in
               match uu____4307 with
               | (head2,uu____4323) ->
                   let uu____4344 =
                     let uu____4345 = FStar_Syntax_Util.un_uinst head2 in
                     uu____4345.FStar_Syntax_Syntax.n in
                   (match uu____4344 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.quote_lid
                        -> true
                    | uu____4349 -> false) in
             let uu____4350 = tc_term (no_inst env2) head1 in
             match uu____4350 with
             | (head2,chead,g_head) ->
                 let uu____4366 =
                   let uu____4373 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____4373
                   then
                     let uu____4380 =
                       let uu____4387 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____4387 in
                     match uu____4380 with | (e1,c,g) -> (e1, c, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2 in
                      let uu____4402 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env3 head2 chead g_head args
                        uu____4402) in
                 (match uu____4366 with
                  | (e1,c,g) ->
                      ((let uu____4415 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____4415
                        then
                          let uu____4416 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____4416
                        else ());
                       (let uu____4418 = comp_check_expected_typ env0 e1 c in
                        match uu____4418 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____4435 =
                                let uu____4436 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____4436.FStar_Syntax_Syntax.n in
                              match uu____4435 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____4440) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___71_4502 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___71_4502.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___71_4502.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___71_4502.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____4551 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____4553 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____4553 in
                            ((let uu____4555 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____4555
                              then
                                let uu____4556 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____4557 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____4556 uu____4557
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____4597 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____4597 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____4617 = tc_term env12 e1 in
                (match uu____4617 with
                 | (e11,c1,g1) ->
                     let uu____4633 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____4643 = FStar_Syntax_Util.type_u () in
                           (match uu____4643 with
                            | (k,uu____4653) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____4655 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____4655, res_t)) in
                     (match uu____4633 with
                      | (env_branches,res_t) ->
                          ((let uu____4665 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____4665
                            then
                              let uu____4666 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____4666
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____4776 =
                              let uu____4781 =
                                FStar_List.fold_right
                                  (fun uu____4853  ->
                                     fun uu____4854  ->
                                       match (uu____4853, uu____4854) with
                                       | ((branch1,f,eff_label,cflags,c,g),
                                          (caccum,gaccum)) ->
                                           let uu____5059 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____5059)) t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____4781 with
                              | (cases,g) ->
                                  let uu____5150 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____5150, g) in
                            match uu____4776 with
                            | (c_branches,g_branches) ->
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
                                           (fun uu____5264  ->
                                              match uu____5264 with
                                              | ((pat,wopt,br),uu____5300,eff_label,uu____5302,uu____5303,uu____5304)
                                                  ->
                                                  let uu____5325 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      res_t in
                                                  (pat, wopt, uu____5325))) in
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
                                  let uu____5380 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____5380
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____5387 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____5387 in
                                     let lb =
                                       let uu____5391 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_Syntax_Syntax.eff_name in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (FStar_Util.Inl guard_x);
                                         FStar_Syntax_Syntax.lbunivs = [];
                                         FStar_Syntax_Syntax.lbtyp =
                                           (c1.FStar_Syntax_Syntax.res_typ);
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____5391;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____5395 =
                                         let uu____5398 =
                                           let uu____5399 =
                                             let uu____5412 =
                                               let uu____5413 =
                                                 let uu____5414 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____5414] in
                                               FStar_Syntax_Subst.close
                                                 uu____5413 e_match in
                                             ((false, [lb]), uu____5412) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____5399 in
                                         FStar_Syntax_Syntax.mk uu____5398 in
                                       uu____5395
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____5427 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____5427
                                  then
                                    let uu____5428 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____5429 =
                                      FStar_Syntax_Print.lcomp_to_string cres in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____5428 uu____5429
                                  else ());
                                 (let uu____5431 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____5431))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5434;
                FStar_Syntax_Syntax.lbunivs = uu____5435;
                FStar_Syntax_Syntax.lbtyp = uu____5436;
                FStar_Syntax_Syntax.lbeff = uu____5437;
                FStar_Syntax_Syntax.lbdef = uu____5438;_}::[]),uu____5439)
           ->
           ((let uu____5459 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5459
             then
               let uu____5460 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____5460
             else ());
            (let uu____5462 = FStar_Options.use_two_phase_tc () in
             if uu____5462
             then
               let is_lb_unannotated t =
                 match t.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_let
                     ((uu____5473,lb::[]),uu____5475) ->
                     let uu____5488 =
                       let uu____5489 =
                         FStar_Syntax_Subst.compress
                           lb.FStar_Syntax_Syntax.lbtyp in
                       uu____5489.FStar_Syntax_Syntax.n in
                     uu____5488 = FStar_Syntax_Syntax.Tm_unknown
                 | uu____5492 -> failwith "Impossible" in
               let drop_lbtyp t =
                 match t.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_let ((t1,lb::[]),t2) ->
                     let uu___72_5512 = t in
                     let uu____5513 =
                       let uu____5514 =
                         let uu____5527 =
                           let uu____5534 =
                             let uu____5537 =
                               let uu___73_5538 = lb in
                               let uu____5539 =
                                 FStar_Syntax_Syntax.mk
                                   FStar_Syntax_Syntax.Tm_unknown
                                   FStar_Pervasives_Native.None
                                   (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.pos in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___73_5538.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___73_5538.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = uu____5539;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___73_5538.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___73_5538.FStar_Syntax_Syntax.lbdef)
                               } in
                             [uu____5537] in
                           (t1, uu____5534) in
                         (uu____5527, t2) in
                       FStar_Syntax_Syntax.Tm_let uu____5514 in
                     {
                       FStar_Syntax_Syntax.n = uu____5513;
                       FStar_Syntax_Syntax.pos =
                         (uu___72_5512.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___72_5512.FStar_Syntax_Syntax.vars)
                     }
                 | uu____5552 -> failwith "Impossible" in
               let uu____5553 =
                 check_top_level_let
                   (let uu___74_5562 = env1 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___74_5562.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___74_5562.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___74_5562.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___74_5562.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___74_5562.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___74_5562.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___74_5562.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___74_5562.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___74_5562.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___74_5562.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___74_5562.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___74_5562.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___74_5562.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___74_5562.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___74_5562.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___74_5562.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___74_5562.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___74_5562.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___74_5562.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___74_5562.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___74_5562.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___74_5562.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___74_5562.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___74_5562.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___74_5562.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___74_5562.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___74_5562.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___74_5562.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___74_5562.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___74_5562.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___74_5562.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___74_5562.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___74_5562.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___74_5562.FStar_TypeChecker_Env.dep_graph)
                    }) top in
               match uu____5553 with
               | (lax_top,l,g) ->
                   let lax_top1 =
                     FStar_TypeChecker_Normalize.remove_uvar_solutions env1
                       lax_top in
                   ((let uu____5574 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases") in
                     if uu____5574
                     then
                       let uu____5575 =
                         FStar_Syntax_Print.term_to_string lax_top1 in
                       FStar_Util.print1 "Phase 1: checked %s\n" uu____5575
                     else ());
                    (let uu____5577 =
                       FStar_TypeChecker_Env.should_verify env1 in
                     if uu____5577
                     then
                       let uu____5584 =
                         let uu____5585 = is_lb_unannotated top in
                         if uu____5585 then drop_lbtyp lax_top1 else lax_top1 in
                       check_top_level_let env1 uu____5584
                     else (lax_top1, l, g)))
             else check_top_level_let env1 top))
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____5589),uu____5590) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5605;
                FStar_Syntax_Syntax.lbunivs = uu____5606;
                FStar_Syntax_Syntax.lbtyp = uu____5607;
                FStar_Syntax_Syntax.lbeff = uu____5608;
                FStar_Syntax_Syntax.lbdef = uu____5609;_}::uu____5610),uu____5611)
           ->
           ((let uu____5633 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5633
             then
               let uu____5634 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____5634
             else ());
            (let uu____5636 = FStar_Options.use_two_phase_tc () in
             if uu____5636
             then
               let uu____5643 =
                 check_top_level_let_rec
                   (let uu___75_5652 = env1 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___75_5652.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___75_5652.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___75_5652.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___75_5652.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___75_5652.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___75_5652.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___75_5652.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___75_5652.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___75_5652.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___75_5652.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___75_5652.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___75_5652.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___75_5652.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___75_5652.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___75_5652.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___75_5652.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___75_5652.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___75_5652.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___75_5652.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___75_5652.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___75_5652.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___75_5652.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___75_5652.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___75_5652.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___75_5652.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___75_5652.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___75_5652.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___75_5652.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___75_5652.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___75_5652.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___75_5652.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___75_5652.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___75_5652.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___75_5652.FStar_TypeChecker_Env.dep_graph)
                    }) top in
               match uu____5643 with
               | (lax_top,l,g) ->
                   let lax_top1 =
                     FStar_TypeChecker_Normalize.remove_uvar_solutions env1
                       lax_top in
                   ((let uu____5664 =
                       FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TwoPhases") in
                     if uu____5664
                     then
                       let uu____5665 =
                         FStar_Syntax_Print.term_to_string lax_top1 in
                       FStar_Util.print1 "Phase 1: checked %s\n" uu____5665
                     else ());
                    (let uu____5667 =
                       FStar_TypeChecker_Env.should_verify env1 in
                     if uu____5667
                     then check_top_level_let_rec env1 lax_top1
                     else (lax_top1, l, g)))
             else check_top_level_let_rec env1 top))
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____5676),uu____5677) ->
           check_inner_let_rec env1 top)
and tc_synth:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun args  ->
      fun rng  ->
        let uu____5703 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5793))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5853))::(uu____5854,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____5855))::
              (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____5928 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_SynthByTacticError,
                  "synth_by_tactic: bad application") rng in
        match uu____5703 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____6012 = FStar_TypeChecker_Env.expected_typ env in
                  (match uu____6012 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____6018 = FStar_TypeChecker_Env.get_range env in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_SynthByTacticError,
                           "synth_by_tactic: need a type annotation when no expected type is present")
                         uu____6018) in
            let uu____6021 = FStar_TypeChecker_Env.clear_expected_typ env in
            (match uu____6021 with
             | (env',uu____6035) ->
                 let uu____6040 = tc_term env' typ in
                 (match uu____6040 with
                  | (typ1,uu____6054,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____6057 = tc_tactic env' tau in
                        match uu____6057 with
                        | (tau1,uu____6071,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let t =
                                if env.FStar_TypeChecker_Env.nosynth
                                then
                                  let uu____6079 =
                                    let uu____6080 =
                                      FStar_TypeChecker_Util.fvar_const env
                                        FStar_Parser_Const.magic_lid in
                                    let uu____6081 =
                                      let uu____6082 =
                                        FStar_Syntax_Syntax.as_arg
                                          FStar_Syntax_Util.exp_unit in
                                      [uu____6082] in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____6080
                                      uu____6081 in
                                  uu____6079 FStar_Pervasives_Native.None rng
                                else
                                  (let t =
                                     env.FStar_TypeChecker_Env.synth env'
                                       typ1 tau1 in
                                   (let uu____6088 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Tac") in
                                    if uu____6088
                                    then
                                      let uu____6089 =
                                        FStar_Syntax_Print.term_to_string t in
                                      FStar_Util.print1 "Got %s\n" uu____6089
                                    else ());
                                   t) in
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____6092 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng in
                               tc_term env uu____6092)))))))
and tc_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___76_6096 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___76_6096.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___76_6096.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___76_6096.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___76_6096.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___76_6096.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___76_6096.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___76_6096.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___76_6096.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___76_6096.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___76_6096.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___76_6096.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___76_6096.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___76_6096.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___76_6096.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___76_6096.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___76_6096.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___76_6096.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___76_6096.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___76_6096.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___76_6096.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___76_6096.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___76_6096.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___76_6096.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___76_6096.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___76_6096.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___76_6096.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___76_6096.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___76_6096.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___76_6096.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___76_6096.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___76_6096.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___76_6096.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___76_6096.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___76_6096.FStar_TypeChecker_Env.dep_graph)
        } in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit
and tc_reified_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___77_6100 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___77_6100.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___77_6100.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___77_6100.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___77_6100.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___77_6100.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___77_6100.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___77_6100.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___77_6100.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___77_6100.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___77_6100.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___77_6100.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___77_6100.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___77_6100.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___77_6100.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___77_6100.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___77_6100.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___77_6100.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___77_6100.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___77_6100.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___77_6100.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___77_6100.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___77_6100.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___77_6100.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___77_6100.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___77_6100.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___77_6100.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___77_6100.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___77_6100.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___77_6100.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___77_6100.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___77_6100.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___77_6100.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___77_6100.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___77_6100.FStar_TypeChecker_Env.dep_graph)
        } in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tac_unit
and tc_tactic_opt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun topt  ->
      match topt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some tactic ->
          let uu____6116 = tc_tactic env tactic in
          (match uu____6116 with
           | (tactic1,uu____6126,uu____6127) ->
               FStar_Pervasives_Native.Some tactic1)
and tc_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t =
        let uu____6166 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____6166 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____6187 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____6187
              then FStar_Util.Inl t1
              else
                (let uu____6193 =
                   let uu____6194 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____6194 in
                 FStar_Util.Inr uu____6193) in
            let is_data_ctor uu___61_6204 =
              match uu___61_6204 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____6207) -> true
              | uu____6214 -> false in
            let uu____6217 =
              (is_data_ctor dc) &&
                (let uu____6219 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____6219) in
            if uu____6217
            then
              let uu____6226 =
                let uu____6231 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____6231) in
              let uu____6232 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____6226 uu____6232
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____6249 =
            let uu____6250 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____6250 in
          failwith uu____6249
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____6284 =
              let uu____6285 = FStar_Syntax_Subst.compress t1 in
              uu____6285.FStar_Syntax_Syntax.n in
            match uu____6284 with
            | FStar_Syntax_Syntax.Tm_arrow uu____6288 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____6301 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___78_6339 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___78_6339.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___78_6339.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___78_6339.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____6391 =
            let uu____6404 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____6404 with
            | FStar_Pervasives_Native.None  ->
                let uu____6419 = FStar_Syntax_Util.type_u () in
                (match uu____6419 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____6391 with
           | (t,uu____6456,g0) ->
               let uu____6470 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____6470 with
                | (e1,uu____6490,g1) ->
                    let uu____6504 =
                      let uu____6505 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____6505
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____6506 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____6504, uu____6506)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____6508 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____6521 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____6521)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____6508 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___79_6540 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___79_6540.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___79_6540.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____6543 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____6543 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____6564 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____6564
                       then FStar_Util.Inl t1
                       else
                         (let uu____6570 =
                            let uu____6571 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____6571 in
                          FStar_Util.Inr uu____6570) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6577;
             FStar_Syntax_Syntax.vars = uu____6578;_},uu____6579)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____6584 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____6584
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____6592 = FStar_TypeChecker_Env.get_range env1 in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____6592
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6600;
             FStar_Syntax_Syntax.vars = uu____6601;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____6610 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6610 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____6633 =
                     let uu____6638 =
                       let uu____6639 = FStar_Syntax_Print.fv_to_string fv in
                       let uu____6640 =
                         FStar_Util.string_of_int (FStar_List.length us1) in
                       let uu____6641 =
                         FStar_Util.string_of_int (FStar_List.length us') in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____6639 uu____6640 uu____6641 in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____6638) in
                   let uu____6642 = FStar_TypeChecker_Env.get_range env1 in
                   FStar_Errors.raise_error uu____6633 uu____6642)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____6658 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6662 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6662 us1 in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6664 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6664 with
           | ((us,t),range) ->
               ((let uu____6687 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____6687
                 then
                   let uu____6688 =
                     let uu____6689 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____6689 in
                   let uu____6690 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____6691 = FStar_Range.string_of_range range in
                   let uu____6692 = FStar_Range.string_of_use_range range in
                   let uu____6693 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____6688 uu____6690 uu____6691 uu____6692 uu____6693
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6698 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6698 us in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant env1 top.FStar_Syntax_Syntax.pos c in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6722 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6722 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____6736 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____6736 with
                | (env2,uu____6750) ->
                    let uu____6755 = tc_binders env2 bs1 in
                    (match uu____6755 with
                     | (bs2,env3,g,us) ->
                         let uu____6774 = tc_comp env3 c1 in
                         (match uu____6774 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___80_6793 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___80_6793.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___80_6793.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____6802 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____6802 in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g1))))))
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
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____6821 =
            let uu____6826 =
              let uu____6827 = FStar_Syntax_Syntax.mk_binder x in
              [uu____6827] in
            FStar_Syntax_Subst.open_term uu____6826 phi in
          (match uu____6821 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____6837 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____6837 with
                | (env2,uu____6851) ->
                    let uu____6856 =
                      let uu____6869 = FStar_List.hd x1 in
                      tc_binder env2 uu____6869 in
                    (match uu____6856 with
                     | (x2,env3,f1,u) ->
                         ((let uu____6897 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____6897
                           then
                             let uu____6898 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____6899 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____6900 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____6898 uu____6899 uu____6900
                           else ());
                          (let uu____6902 = FStar_Syntax_Util.type_u () in
                           match uu____6902 with
                           | (t_phi,uu____6914) ->
                               let uu____6915 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____6915 with
                                | (phi2,uu____6929,f2) ->
                                    let e1 =
                                      let uu___81_6934 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___81_6934.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___81_6934.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____6941 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____6941 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____6954) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____6977 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____6977
            then
              let uu____6978 =
                FStar_Syntax_Print.term_to_string
                  (let uu___82_6981 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___82_6981.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___82_6981.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____6978
            else ());
           (let uu____6987 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____6987 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____7000 ->
          let uu____7001 =
            let uu____7002 = FStar_Syntax_Print.term_to_string top in
            let uu____7003 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____7002
              uu____7003 in
          failwith uu____7001
and tc_constant:
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____7013 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____7014,FStar_Pervasives_Native.None ) ->
            FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____7025,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____7041 -> FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_float uu____7046 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____7047 ->
            let uu____7048 =
              let uu____7053 =
                FStar_ToSyntax_Env.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid in
              FStar_All.pipe_right uu____7053 FStar_Util.must in
            FStar_All.pipe_right uu____7048 FStar_Pervasives_Native.fst
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____7078 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____7079 =
              let uu____7084 =
                let uu____7085 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7085 in
              (FStar_Errors.Fatal_IllTyped, uu____7084) in
            FStar_Errors.raise_error uu____7079 r
        | FStar_Const.Const_set_range_of  ->
            let uu____7086 =
              let uu____7091 =
                let uu____7092 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7092 in
              (FStar_Errors.Fatal_IllTyped, uu____7091) in
            FStar_Errors.raise_error uu____7086 r
        | FStar_Const.Const_reify  ->
            let uu____7093 =
              let uu____7098 =
                let uu____7099 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7099 in
              (FStar_Errors.Fatal_IllTyped, uu____7098) in
            FStar_Errors.raise_error uu____7093 r
        | FStar_Const.Const_reflect uu____7100 ->
            let uu____7101 =
              let uu____7106 =
                let uu____7107 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____7107 in
              (FStar_Errors.Fatal_IllTyped, uu____7106) in
            FStar_Errors.raise_error uu____7101 r
        | uu____7108 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedConstant,
                "Unsupported constant") r
and tc_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.universe,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun c  ->
      let c0 = c in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uu____7125) ->
          let uu____7134 = FStar_Syntax_Util.type_u () in
          (match uu____7134 with
           | (k,u) ->
               let uu____7147 = tc_check_tot_or_gtot_term env t k in
               (match uu____7147 with
                | (t1,uu____7161,g) ->
                    let uu____7163 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____7163, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____7165) ->
          let uu____7174 = FStar_Syntax_Util.type_u () in
          (match uu____7174 with
           | (k,u) ->
               let uu____7187 = tc_check_tot_or_gtot_term env t k in
               (match uu____7187 with
                | (t1,uu____7201,g) ->
                    let uu____7203 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____7203, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head1 =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          let head2 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head1
            | us ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_uinst (head1, us))
                  FStar_Pervasives_Native.None c0.FStar_Syntax_Syntax.pos in
          let tc =
            let uu____7211 =
              let uu____7212 =
                let uu____7213 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____7213 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____7212 in
            uu____7211 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____7216 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____7216 with
           | (tc1,uu____7230,f) ->
               let uu____7232 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____7232 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____7276 =
                        let uu____7277 = FStar_Syntax_Subst.compress head3 in
                        uu____7277.FStar_Syntax_Syntax.n in
                      match uu____7276 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____7280,us) -> us
                      | uu____7286 -> [] in
                    let uu____7287 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____7287 with
                     | (uu____7308,args1) ->
                         let uu____7330 =
                           let uu____7349 = FStar_List.hd args1 in
                           let uu____7362 = FStar_List.tl args1 in
                           (uu____7349, uu____7362) in
                         (match uu____7330 with
                          | (res,args2) ->
                              let uu____7427 =
                                let uu____7436 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___62_7464  ->
                                          match uu___62_7464 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____7472 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____7472 with
                                               | (env1,uu____7484) ->
                                                   let uu____7489 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____7489 with
                                                    | (e1,uu____7501,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____7436
                                  FStar_List.unzip in
                              (match uu____7427 with
                               | (flags1,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___83_7540 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___83_7540.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___83_7540.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____7544 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____7544 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____7548 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____7548))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____7556 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____7557 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____7567 = aux u3 in FStar_Syntax_Syntax.U_succ uu____7567
        | FStar_Syntax_Syntax.U_max us ->
            let uu____7571 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____7571
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____7576 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____7576 FStar_Pervasives_Native.snd
         | uu____7585 -> aux u)
and tc_abs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun top  ->
      fun bs  ->
        fun body  ->
          let fail msg t =
            let uu____7609 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top in
            FStar_Errors.raise_error uu____7609 top.FStar_Syntax_Syntax.pos in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____7703 bs2 bs_expected1 =
              match uu____7703 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____7871)) ->
                             let uu____7876 =
                               let uu____7881 =
                                 let uu____7882 =
                                   FStar_Syntax_Print.bv_to_string hd1 in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____7882 in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____7881) in
                             let uu____7883 =
                               FStar_Syntax_Syntax.range_of_bv hd1 in
                             FStar_Errors.raise_error uu____7876 uu____7883
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____7884),FStar_Pervasives_Native.None ) ->
                             let uu____7889 =
                               let uu____7894 =
                                 let uu____7895 =
                                   FStar_Syntax_Print.bv_to_string hd1 in
                                 FStar_Util.format1
                                   "Inconsistent implicit argument annotation on argument %s"
                                   uu____7895 in
                               (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                                 uu____7894) in
                             let uu____7896 =
                               FStar_Syntax_Syntax.range_of_bv hd1 in
                             FStar_Errors.raise_error uu____7889 uu____7896
                         | uu____7897 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____7903 =
                           let uu____7908 =
                             let uu____7909 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____7909.FStar_Syntax_Syntax.n in
                           match uu____7908 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____7916 ->
                               ((let uu____7918 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____7918
                                 then
                                   let uu____7919 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____7919
                                 else ());
                                (let uu____7921 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____7921 with
                                 | (t,uu____7933,g1) ->
                                     let g2 =
                                       let uu____7936 =
                                         FStar_TypeChecker_Rel.teq_nosmt env2
                                           t expected_t in
                                       if uu____7936
                                       then
                                         FStar_TypeChecker_Rel.trivial_guard
                                       else
                                         (let uu____7938 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t in
                                          match uu____7938 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____7941 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t in
                                              let uu____7946 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2 in
                                              FStar_Errors.raise_error
                                                uu____7941 uu____7946
                                          | FStar_Pervasives_Native.Some g2
                                              ->
                                              let uu____7948 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____7948
                                                "Type annotation on parameter incompatible with the expected type"
                                                g2) in
                                     let g3 =
                                       let uu____7950 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____7950 in
                                     (t, g3))) in
                         match uu____7903 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___84_7978 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___84_7978.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___84_7978.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____7991 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____7991 in
                             aux (env3, (b :: out), g1, subst2) bs3
                               bs_expected2))
                   | (rest,[]) ->
                       (env2, (FStar_List.rev out),
                         (FStar_Pervasives_Native.Some (FStar_Util.Inl rest)),
                         g, subst1)
                   | ([],rest) ->
                       (env2, (FStar_List.rev out),
                         (FStar_Pervasives_Native.Some (FStar_Util.Inr rest)),
                         g, subst1)) in
            aux (env1, [], FStar_TypeChecker_Rel.trivial_guard, []) bs1
              bs_expected in
          let rec expected_function_typ1 env1 t0 body1 =
            match t0 with
            | FStar_Pervasives_Native.None  ->
                ((match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____8139 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____8148 = tc_binders env1 bs in
                  match uu____8148 with
                  | (bs1,envbody,g,uu____8178) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____8222 =
                    let uu____8223 = FStar_Syntax_Subst.compress t2 in
                    uu____8223.FStar_Syntax_Syntax.n in
                  match uu____8222 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____8246 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8270 -> failwith "Impossible");
                       (let uu____8279 = tc_binders env1 bs in
                        match uu____8279 with
                        | (bs1,envbody,g,uu____8311) ->
                            let uu____8312 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____8312 with
                             | (envbody1,uu____8340) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____8351;
                         FStar_Syntax_Syntax.pos = uu____8352;
                         FStar_Syntax_Syntax.vars = uu____8353;_},uu____8354)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8398 -> failwith "Impossible");
                       (let uu____8407 = tc_binders env1 bs in
                        match uu____8407 with
                        | (bs1,envbody,g,uu____8439) ->
                            let uu____8440 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____8440 with
                             | (envbody1,uu____8468) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____8480) ->
                      let uu____8485 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____8485 with
                       | (uu____8526,bs1,bs',copt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____8569 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____8569 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____8678 c_expected2 body3
                               =
                               match uu____8678 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____8798 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____8798, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____8829 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____8829 in
                                        let uu____8830 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____8830, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        let uu____8855 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c) in
                                        if uu____8855
                                        then
                                          let t3 =
                                            FStar_TypeChecker_Normalize.unfold_whnf
                                              env3
                                              (FStar_Syntax_Util.comp_result
                                                 c) in
                                          (match t3.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs_expected3,c_expected3) ->
                                               let uu____8907 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____8907 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____8930 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____8930 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____8980 =
                                                           let uu____9011 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____9011,
                                                             subst2) in
                                                         handle_more
                                                           uu____8980
                                                           c_expected4 body3))
                                           | uu____9028 ->
                                               let body4 =
                                                 FStar_Syntax_Util.abs
                                                   more_bs body3
                                                   FStar_Pervasives_Native.None in
                                               (env3, bs2, guard, c, body4))
                                        else
                                          (let body4 =
                                             FStar_Syntax_Util.abs more_bs
                                               body3
                                               FStar_Pervasives_Native.None in
                                           (env3, bs2, guard, c, body4))) in
                             let uu____9044 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____9044 c_expected1 body2 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___85_9101 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___85_9101.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___85_9101.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___85_9101.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___85_9101.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___85_9101.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___85_9101.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___85_9101.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___85_9101.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___85_9101.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___85_9101.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___85_9101.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___85_9101.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___85_9101.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___85_9101.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___85_9101.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___85_9101.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___85_9101.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___85_9101.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___85_9101.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___85_9101.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___85_9101.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___85_9101.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___85_9101.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___85_9101.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___85_9101.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___85_9101.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___85_9101.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___85_9101.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___85_9101.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___85_9101.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___85_9101.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___85_9101.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___85_9101.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___85_9101.FStar_TypeChecker_Env.dep_graph)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____9149  ->
                                     fun uu____9150  ->
                                       match (uu____9149, uu____9150) with
                                       | ((env2,letrec_binders),(l,t3,u_names))
                                           ->
                                           let uu____9212 =
                                             let uu____9219 =
                                               let uu____9220 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____9220
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____9219 t3 in
                                           (match uu____9212 with
                                            | (t4,uu____9242,uu____9243) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (u_names, t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____9253 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___86_9256 =
                                                             x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___86_9256.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___86_9256.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____9253 ::
                                                        letrec_binders
                                                  | uu____9257 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____9262 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1 in
                           (match uu____9262 with
                            | (envbody,bs1,g,c,body2) ->
                                let uu____9316 = mk_letrec_env envbody bs1 c in
                                (match uu____9316 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, g))))
                  | uu____9362 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____9383 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____9383
                      else
                        (let uu____9385 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1 in
                         match uu____9385 with
                         | (uu____9424,bs1,uu____9426,c_opt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____9446 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____9446 with
          | (env1,topt) ->
              ((let uu____9466 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____9466
                then
                  let uu____9467 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____9467
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____9471 = expected_function_typ1 env1 topt body in
                match uu____9471 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let uu____9511 =
                      let should_check_expected_effect =
                        let uu____9519 =
                          let uu____9526 =
                            let uu____9527 =
                              FStar_Syntax_Subst.compress body1 in
                            uu____9527.FStar_Syntax_Syntax.n in
                          (c_opt, uu____9526) in
                        match uu____9519 with
                        | (FStar_Pervasives_Native.None
                           ,FStar_Syntax_Syntax.Tm_ascribed
                           (uu____9532,(FStar_Util.Inr expected_c,uu____9534),uu____9535))
                            -> false
                        | uu____9584 -> true in
                      let uu____9591 =
                        tc_term
                          (let uu___87_9600 = envbody in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___87_9600.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___87_9600.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___87_9600.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___87_9600.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___87_9600.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___87_9600.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___87_9600.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___87_9600.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___87_9600.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___87_9600.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___87_9600.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___87_9600.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___87_9600.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = false;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___87_9600.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq = use_eq;
                             FStar_TypeChecker_Env.is_iface =
                               (uu___87_9600.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___87_9600.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___87_9600.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___87_9600.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___87_9600.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___87_9600.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___87_9600.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___87_9600.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___87_9600.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___87_9600.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___87_9600.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qname_and_index =
                               (uu___87_9600.FStar_TypeChecker_Env.qname_and_index);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___87_9600.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth =
                               (uu___87_9600.FStar_TypeChecker_Env.synth);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___87_9600.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___87_9600.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___87_9600.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___87_9600.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___87_9600.FStar_TypeChecker_Env.dep_graph)
                           }) body1 in
                      match uu____9591 with
                      | (body2,cbody,guard_body) ->
                          let guard_body1 =
                            FStar_TypeChecker_Rel.solve_deferred_constraints
                              envbody guard_body in
                          if should_check_expected_effect
                          then
                            let uu____9617 =
                              let uu____9624 =
                                let uu____9629 =
                                  FStar_Syntax_Syntax.lcomp_comp cbody in
                                (body2, uu____9629) in
                              check_expected_effect
                                (let uu___88_9632 = envbody in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___88_9632.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___88_9632.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___88_9632.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___88_9632.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___88_9632.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___88_9632.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___88_9632.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___88_9632.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___88_9632.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___88_9632.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___88_9632.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___88_9632.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___88_9632.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___88_9632.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___88_9632.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___88_9632.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___88_9632.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___88_9632.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___88_9632.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___88_9632.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___88_9632.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___88_9632.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___88_9632.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___88_9632.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___88_9632.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___88_9632.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___88_9632.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___88_9632.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___88_9632.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___88_9632.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___88_9632.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___88_9632.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___88_9632.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___88_9632.FStar_TypeChecker_Env.dep_graph)
                                 }) c_opt uu____9624 in
                            (match uu____9617 with
                             | (body3,cbody1,guard) ->
                                 let uu____9642 =
                                   FStar_TypeChecker_Rel.conj_guard
                                     guard_body1 guard in
                                 (body3, cbody1, uu____9642))
                          else
                            (let uu____9644 =
                               FStar_Syntax_Syntax.lcomp_comp cbody in
                             (body2, uu____9644, guard_body1)) in
                    (match uu____9511 with
                     | (body2,cbody,guard) ->
                         let guard1 =
                           let uu____9655 =
                             env1.FStar_TypeChecker_Env.top_level ||
                               (let uu____9657 =
                                  FStar_TypeChecker_Env.should_verify env1 in
                                Prims.op_Negation uu____9657) in
                           if uu____9655
                           then
                             let uu____9658 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             FStar_TypeChecker_Rel.discharge_guard envbody
                               uu____9658
                           else
                             (let guard1 =
                                let uu____9661 =
                                  FStar_TypeChecker_Rel.conj_guard g guard in
                                FStar_TypeChecker_Rel.close_guard env1
                                  (FStar_List.append bs1 letrec_binders)
                                  uu____9661 in
                              guard1) in
                         let tfun_computed =
                           FStar_Syntax_Util.arrow bs1 cbody in
                         let e =
                           FStar_Syntax_Util.abs bs1 body2
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp
                                   (FStar_Util.dflt cbody c_opt))) in
                         let uu____9670 =
                           match tfun_opt with
                           | FStar_Pervasives_Native.Some t ->
                               let t1 = FStar_Syntax_Subst.compress t in
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_arrow uu____9691 ->
                                    (e, t1, guard1)
                                | uu____9704 ->
                                    let uu____9705 =
                                      FStar_TypeChecker_Util.check_and_ascribe
                                        env1 e tfun_computed t1 in
                                    (match uu____9705 with
                                     | (e1,guard') ->
                                         let uu____9718 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 guard' in
                                         (e1, t1, uu____9718)))
                           | FStar_Pervasives_Native.None  ->
                               (e, tfun_computed, guard1) in
                         (match uu____9670 with
                          | (e1,tfun,guard2) ->
                              let c = FStar_Syntax_Syntax.mk_Total tfun in
                              let uu____9731 =
                                let uu____9736 =
                                  FStar_Syntax_Util.lcomp_of_comp c in
                                FStar_TypeChecker_Util.strengthen_precondition
                                  FStar_Pervasives_Native.None env1 e1
                                  uu____9736 guard2 in
                              (match uu____9731 with
                               | (c1,g1) -> (e1, c1, g1))))))
and check_application_args:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
                FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun ghead  ->
          fun args  ->
            fun expected_topt  ->
              let n_args = FStar_List.length args in
              let r = FStar_TypeChecker_Env.get_range env in
              let thead = chead.FStar_Syntax_Syntax.res_typ in
              (let uu____9781 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____9781
               then
                 let uu____9782 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____9783 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____9782
                   uu____9783
               else ());
              (let monadic_application uu____9840 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____9840 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___89_9899 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___89_9899.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___89_9899.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp_thunk =
                           (uu___89_9899.FStar_Syntax_Syntax.comp_thunk)
                       } in
                     let uu____9900 =
                       match bs with
                       | [] ->
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres1, g)
                       | uu____9914 ->
                           let g =
                             let uu____9922 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____9922
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____9923 =
                             let uu____9924 =
                               let uu____9927 =
                                 let uu____9928 =
                                   FStar_Syntax_Syntax.lcomp_comp cres1 in
                                 FStar_Syntax_Util.arrow bs uu____9928 in
                               FStar_Syntax_Syntax.mk_Total uu____9927 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____9924 in
                           (uu____9923, g) in
                     (match uu____9900 with
                      | (cres2,guard1) ->
                          ((let uu____9942 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____9942
                            then
                              let uu____9943 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____9943
                            else ());
                           (let cres3 =
                              let head_is_pure_and_some_arg_is_effectful =
                                (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                   chead1)
                                  &&
                                  (FStar_Util.for_some
                                     (fun uu____9959  ->
                                        match uu____9959 with
                                        | (uu____9968,uu____9969,lc) ->
                                            (let uu____9977 =
                                               FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                 lc in
                                             Prims.op_Negation uu____9977) ||
                                              (FStar_TypeChecker_Util.should_not_inline_lc
                                                 lc)) arg_comps_rev) in
                              let term =
                                FStar_Syntax_Syntax.mk_Tm_app head2
                                  (FStar_List.rev arg_rets_rev)
                                  FStar_Pervasives_Native.None
                                  head2.FStar_Syntax_Syntax.pos in
                              let uu____9987 =
                                (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                   cres2)
                                  && head_is_pure_and_some_arg_is_effectful in
                              if uu____9987
                              then
                                ((let uu____9989 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme in
                                  if uu____9989
                                  then
                                    let uu____9990 =
                                      FStar_Syntax_Print.term_to_string term in
                                    FStar_Util.print1
                                      "(a) Monadic app: Return inserted in monadic application: %s\n"
                                      uu____9990
                                  else ());
                                 FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                   env term cres2)
                              else
                                ((let uu____9994 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme in
                                  if uu____9994
                                  then
                                    let uu____9995 =
                                      FStar_Syntax_Print.term_to_string term in
                                    FStar_Util.print1
                                      "(a) Monadic app: No return inserted in monadic application: %s\n"
                                      uu____9995
                                  else ());
                                 cres2) in
                            let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____10019  ->
                                     match uu____10019 with
                                     | ((e,q),x,c) ->
                                         ((let uu____10045 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme in
                                           if uu____10045
                                           then
                                             let uu____10046 =
                                               match x with
                                               | FStar_Pervasives_Native.None
                                                    -> "_"
                                               | FStar_Pervasives_Native.Some
                                                   x1 ->
                                                   FStar_Syntax_Print.bv_to_string
                                                     x1 in
                                             let uu____10048 =
                                               FStar_Syntax_Print.term_to_string
                                                 e in
                                             FStar_Util.print2
                                               "(b) Monadic app: Binding argument %s : %s\n"
                                               uu____10046 uu____10048
                                           else ());
                                          (let uu____10050 =
                                             FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                               c in
                                           if uu____10050
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
                                arg_comps_rev in
                            let comp1 =
                              (let uu____10058 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Extreme in
                               if uu____10058
                               then
                                 let uu____10059 =
                                   FStar_Syntax_Print.term_to_string head2 in
                                 FStar_Util.print1
                                   "(c) Monadic app: Binding head %s "
                                   uu____10059
                               else ());
                              (let uu____10061 =
                                 FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                   chead1 in
                               if uu____10061
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
                              FStar_TypeChecker_Util.subst_lcomp subst1 comp1 in
                            let shortcuts_evaluation_order =
                              let uu____10069 =
                                let uu____10070 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____10070.FStar_Syntax_Syntax.n in
                              match uu____10069 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____10074 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____10095  ->
                                         match uu____10095 with
                                         | (arg,uu____10109,uu____10110) ->
                                             arg :: args1) [] arg_comps_rev in
                                let app =
                                  FStar_Syntax_Syntax.mk_Tm_app head2 args1
                                    FStar_Pervasives_Native.None r in
                                let app1 =
                                  FStar_TypeChecker_Util.maybe_lift env app
                                    cres3.FStar_Syntax_Syntax.eff_name
                                    comp2.FStar_Syntax_Syntax.eff_name
                                    comp2.FStar_Syntax_Syntax.res_typ in
                                FStar_TypeChecker_Util.maybe_monadic env app1
                                  comp2.FStar_Syntax_Syntax.eff_name
                                  comp2.FStar_Syntax_Syntax.res_typ
                              else
                                (let uu____10120 =
                                   let map_fun uu____10182 =
                                     match uu____10182 with
                                     | ((e,q),uu____10217,c) ->
                                         let uu____10227 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____10227
                                         then
                                           (FStar_Pervasives_Native.None,
                                             (e, q))
                                         else
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
                                            let uu____10277 =
                                              let uu____10282 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____10282, q) in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____10277)) in
                                   let uu____10311 =
                                     let uu____10336 =
                                       let uu____10359 =
                                         let uu____10374 =
                                           let uu____10383 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____10383,
                                             FStar_Pervasives_Native.None,
                                             chead1) in
                                         uu____10374 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____10359 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____10336 in
                                   match uu____10311 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____10556 =
                                         let uu____10557 =
                                           FStar_List.hd reverse_args in
                                         FStar_Pervasives_Native.fst
                                           uu____10557 in
                                       let uu____10566 =
                                         let uu____10573 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____10573 in
                                       (lifted_args, uu____10556,
                                         uu____10566) in
                                 match uu____10120 with
                                 | (lifted_args,head3,args1) ->
                                     let app =
                                       FStar_Syntax_Syntax.mk_Tm_app head3
                                         args1 FStar_Pervasives_Native.None r in
                                     let app1 =
                                       FStar_TypeChecker_Util.maybe_lift env
                                         app
                                         cres3.FStar_Syntax_Syntax.eff_name
                                         comp2.FStar_Syntax_Syntax.eff_name
                                         comp2.FStar_Syntax_Syntax.res_typ in
                                     let app2 =
                                       FStar_TypeChecker_Util.maybe_monadic
                                         env app1
                                         comp2.FStar_Syntax_Syntax.eff_name
                                         comp2.FStar_Syntax_Syntax.res_typ in
                                     let bind_lifted_args e uu___63_10676 =
                                       match uu___63_10676 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____10731 =
                                               let uu____10734 =
                                                 let uu____10735 =
                                                   let uu____10748 =
                                                     let uu____10749 =
                                                       let uu____10750 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____10750] in
                                                     FStar_Syntax_Subst.close
                                                       uu____10749 e in
                                                   ((false, [lb]),
                                                     uu____10748) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____10735 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10734 in
                                             uu____10731
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
                                     FStar_List.fold_left bind_lifted_args
                                       app2 lifted_args) in
                            let uu____10780 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp2
                                guard1 in
                            match uu____10780 with
                            | (comp3,g) ->
                                ((let uu____10796 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.Extreme in
                                  if uu____10796
                                  then
                                    let uu____10797 =
                                      FStar_Syntax_Print.term_to_string app in
                                    let uu____10798 =
                                      FStar_Syntax_Print.lcomp_to_string
                                        comp3 in
                                    FStar_Util.print2
                                      "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                      uu____10797 uu____10798
                                  else ());
                                 (app, comp3, g))))) in
               let rec tc_args head_info uu____10876 bs args1 =
                 match uu____10876 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____11023))::rest,
                         (uu____11025,FStar_Pervasives_Native.None )::uu____11026)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t in
                          let uu____11087 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____11087 with
                           | (varg,uu____11107,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____11129 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____11129) in
                               let uu____11130 =
                                 let uu____11165 =
                                   let uu____11180 =
                                     let uu____11193 =
                                       let uu____11194 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____11194
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____11193) in
                                   uu____11180 :: outargs in
                                 let uu____11213 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____11165, (arg :: arg_rets),
                                   uu____11213, fvs) in
                               tc_args head_info uu____11130 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____11315),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11316)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____11329 ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier")
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___90_11340 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___90_11340.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___90_11340.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____11342 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____11342
                             then
                               let uu____11343 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____11343
                             else ());
                            (let targ1 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___91_11348 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___91_11348.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___91_11348.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___91_11348.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___91_11348.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___91_11348.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___91_11348.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___91_11348.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___91_11348.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___91_11348.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___91_11348.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___91_11348.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___91_11348.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___91_11348.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___91_11348.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___91_11348.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___91_11348.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___91_11348.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___91_11348.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___91_11348.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___91_11348.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___91_11348.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___91_11348.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___91_11348.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___91_11348.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___91_11348.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___91_11348.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___91_11348.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___91_11348.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___91_11348.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___91_11348.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___91_11348.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___91_11348.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___91_11348.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___91_11348.FStar_TypeChecker_Env.dep_graph)
                               } in
                             (let uu____11350 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____11350
                              then
                                let uu____11351 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____11352 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11353 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____11351 uu____11352 uu____11353
                              else ());
                             (let uu____11355 = tc_term env2 e in
                              match uu____11355 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____11390 =
                                      let uu____11393 =
                                        let uu____11400 =
                                          FStar_Syntax_Syntax.bv_to_name x1 in
                                        FStar_Syntax_Syntax.as_arg
                                          uu____11400 in
                                      FStar_Pervasives_Native.fst uu____11393 in
                                    (uu____11390, aq) in
                                  let uu____11407 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____11407
                                  then
                                    let subst2 =
                                      let uu____11415 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____11415
                                        e1 in
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
                      | (uu____11541,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____11577) ->
                          let uu____11628 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____11628 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____11662 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____11662
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____11687 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____11687 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            let uu____11709 =
                                              FStar_Syntax_Util.lcomp_of_comp
                                                cres'1 in
                                            (head2, chead1, ghead1,
                                              uu____11709) in
                                          ((let uu____11711 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____11711
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
                                 | uu____11753 when Prims.op_Negation norm1
                                     ->
                                     let rec norm_tres tres2 =
                                       let tres3 =
                                         FStar_TypeChecker_Normalize.unfold_whnf
                                           env tres2 in
                                       let uu____11759 =
                                         let uu____11760 =
                                           FStar_Syntax_Subst.compress tres3 in
                                         uu____11760.FStar_Syntax_Syntax.n in
                                       match uu____11759 with
                                       | FStar_Syntax_Syntax.Tm_refine
                                           ({
                                              FStar_Syntax_Syntax.ppname =
                                                uu____11763;
                                              FStar_Syntax_Syntax.index =
                                                uu____11764;
                                              FStar_Syntax_Syntax.sort =
                                                tres4;_},uu____11766)
                                           -> norm_tres tres4
                                       | uu____11773 -> tres3 in
                                     let uu____11774 = norm_tres tres1 in
                                     aux true uu____11774
                                 | uu____11775 ->
                                     let uu____11776 =
                                       let uu____11781 =
                                         let uu____11782 =
                                           FStar_TypeChecker_Normalize.term_to_string
                                             env thead in
                                         let uu____11783 =
                                           FStar_Util.string_of_int n_args in
                                         FStar_Util.format2
                                           "Too many arguments to function of type %s; got %s arguments"
                                           uu____11782 uu____11783 in
                                       (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                         uu____11781) in
                                     let uu____11790 =
                                       FStar_Syntax_Syntax.argpos arg in
                                     FStar_Errors.raise_error uu____11776
                                       uu____11790 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____11809 =
                   let uu____11810 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____11810.FStar_Syntax_Syntax.n in
                 match uu____11809 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____11821 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____11922 = tc_term env1 e in
                           (match uu____11922 with
                            | (e1,c,g_e) ->
                                let uu____11944 = tc_args1 env1 tl1 in
                                (match uu____11944 with
                                 | (args2,comps,g_rest) ->
                                     let uu____11984 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____11984))) in
                     let uu____12005 = tc_args1 env args in
                     (match uu____12005 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____12042 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____12080  ->
                                      match uu____12080 with
                                      | (uu____12093,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____12042 in
                          let ml_or_tot t r1 =
                            let uu____12110 = FStar_Options.ml_ish () in
                            if uu____12110
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____12113 =
                              let uu____12116 =
                                let uu____12117 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____12117
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____12116 in
                            ml_or_tot uu____12113 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____12130 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____12130
                            then
                              let uu____12131 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____12132 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____12133 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____12131 uu____12132 uu____12133
                            else ());
                           (let uu____12136 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____12136);
                           (let comp =
                              let uu____12138 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____12149  ->
                                   fun out  ->
                                     match uu____12149 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____12138 in
                            let uu____12163 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____12166 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____12163, comp, uu____12166))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____12169;
                        FStar_Syntax_Syntax.pos = uu____12170;
                        FStar_Syntax_Syntax.vars = uu____12171;_},uu____12172)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____12293 = tc_term env1 e in
                           (match uu____12293 with
                            | (e1,c,g_e) ->
                                let uu____12315 = tc_args1 env1 tl1 in
                                (match uu____12315 with
                                 | (args2,comps,g_rest) ->
                                     let uu____12355 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____12355))) in
                     let uu____12376 = tc_args1 env args in
                     (match uu____12376 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____12413 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____12451  ->
                                      match uu____12451 with
                                      | (uu____12464,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____12413 in
                          let ml_or_tot t r1 =
                            let uu____12481 = FStar_Options.ml_ish () in
                            if uu____12481
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____12484 =
                              let uu____12487 =
                                let uu____12488 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____12488
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____12487 in
                            ml_or_tot uu____12484 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____12501 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____12501
                            then
                              let uu____12502 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____12503 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____12504 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____12502 uu____12503 uu____12504
                            else ());
                           (let uu____12507 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____12507);
                           (let comp =
                              let uu____12509 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____12520  ->
                                   fun out  ->
                                     match uu____12520 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____12509 in
                            let uu____12534 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____12537 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____12534, comp, uu____12537))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____12558 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____12558 with
                      | (bs1,c1) ->
                          let head_info =
                            let uu____12582 =
                              FStar_Syntax_Util.lcomp_of_comp c1 in
                            (head1, chead, ghead, uu____12582) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____12624) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____12630,uu____12631) -> check_function_app t
                 | uu____12672 ->
                     let uu____12673 =
                       FStar_TypeChecker_Err.expected_function_typ env tf in
                     FStar_Errors.raise_error uu____12673
                       head1.FStar_Syntax_Syntax.pos in
               check_function_app thead)
and check_short_circuit_args:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
                FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun g_head  ->
          fun args  ->
            fun expected_topt  ->
              let r = FStar_TypeChecker_Env.get_range env in
              let tf =
                FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_Syntax_Util.comp_result c in
                  let uu____12747 =
                    FStar_List.fold_left2
                      (fun uu____12790  ->
                         fun uu____12791  ->
                           fun uu____12792  ->
                             match (uu____12790, uu____12791, uu____12792)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                        "Inconsistent implicit qualifiers")
                                      e.FStar_Syntax_Syntax.pos
                                  else ();
                                  (let uu____12860 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____12860 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____12878 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____12878 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____12882 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____12882)
                                              &&
                                              (let uu____12884 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____12884)) in
                                       let uu____12885 =
                                         let uu____12894 =
                                           let uu____12903 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____12903] in
                                         FStar_List.append seen uu____12894 in
                                       let uu____12910 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____12885, uu____12910, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____12747 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r in
                       let c1 =
                         if ghost
                         then
                           let uu____12946 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____12946
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____12948 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____12948 with | (c2,g) -> (e, c2, g)))
              | uu____12965 ->
                  check_application_args env head1 chead g_head args
                    expected_topt
and tc_eqn:
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
          FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple6
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____13007 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____13007 with
        | (pattern,when_clause,branch_exp) ->
            let uu____13051 = branch1 in
            (match uu____13051 with
             | (cpat,uu____13091,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let tc_annot env1 t =
                     let uu____13158 = FStar_Syntax_Util.type_u () in
                     match uu____13158 with
                     | (tu,u) ->
                         let uu____13169 =
                           tc_check_tot_or_gtot_term env1 t tu in
                         (match uu____13169 with
                          | (t1,uu____13181,g) -> (t1, g)) in
                   let uu____13183 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0
                       tc_annot in
                   match uu____13183 with
                   | (pat_bvs1,exp,guard_pat_annots,p) ->
                       ((let uu____13217 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____13217
                         then
                           let uu____13218 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____13219 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____13218 uu____13219
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____13222 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____13222 with
                         | (env1,uu____13244) ->
                             let env11 =
                               let uu___92_13250 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___92_13250.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___92_13250.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___92_13250.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___92_13250.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___92_13250.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___92_13250.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___92_13250.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___92_13250.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___92_13250.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___92_13250.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___92_13250.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___92_13250.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___92_13250.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___92_13250.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___92_13250.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___92_13250.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___92_13250.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___92_13250.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___92_13250.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___92_13250.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___92_13250.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___92_13250.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___92_13250.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___92_13250.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___92_13250.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___92_13250.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___92_13250.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___92_13250.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___92_13250.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___92_13250.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___92_13250.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___92_13250.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___92_13250.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___92_13250.FStar_TypeChecker_Env.dep_graph)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____13253 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____13253
                               then
                                 let uu____13254 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____13255 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____13254 uu____13255
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t in
                               let uu____13258 =
                                 tc_tot_or_gtot_term env12 exp in
                               match uu____13258 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___93_13283 = g in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___93_13283.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___93_13283.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___93_13283.FStar_TypeChecker_Env.implicits)
                                     } in
                                   let uu____13284 =
                                     let uu____13285 =
                                       FStar_TypeChecker_Rel.teq_nosmt env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t in
                                     if uu____13285
                                     then
                                       let env13 =
                                         FStar_TypeChecker_Env.set_range
                                           env12 exp1.FStar_Syntax_Syntax.pos in
                                       let uu____13287 =
                                         FStar_TypeChecker_Rel.discharge_guard_no_smt
                                           env13 g1 in
                                       FStar_All.pipe_right uu____13287
                                         FStar_TypeChecker_Rel.resolve_implicits
                                     else
                                       (let uu____13289 =
                                          let uu____13294 =
                                            let uu____13295 =
                                              FStar_Syntax_Print.term_to_string
                                                lc.FStar_Syntax_Syntax.res_typ in
                                            let uu____13296 =
                                              FStar_Syntax_Print.term_to_string
                                                expected_pat_t in
                                            FStar_Util.format2
                                              "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                              uu____13295 uu____13296 in
                                          (FStar_Errors.Fatal_MismatchedPatternType,
                                            uu____13294) in
                                        FStar_Errors.raise_error uu____13289
                                          exp1.FStar_Syntax_Syntax.pos) in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1 in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____13313 =
                                       let uu____13314 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____13314 in
                                     if uu____13313
                                     then
                                       let unresolved =
                                         let uu____13326 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____13326
                                           FStar_Util.set_elements in
                                       let uu____13353 =
                                         let uu____13358 =
                                           let uu____13359 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env norm_exp in
                                           let uu____13360 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env expected_pat_t in
                                           let uu____13361 =
                                             let uu____13362 =
                                               FStar_All.pipe_right
                                                 unresolved
                                                 (FStar_List.map
                                                    (fun uu____13380  ->
                                                       match uu____13380 with
                                                       | (u,uu____13386) ->
                                                           FStar_Syntax_Print.uvar_to_string
                                                             u)) in
                                             FStar_All.pipe_right uu____13362
                                               (FStar_String.concat ", ") in
                                           FStar_Util.format3
                                             "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                             uu____13359 uu____13360
                                             uu____13361 in
                                         (FStar_Errors.Fatal_UnresolvedPatternVar,
                                           uu____13358) in
                                       FStar_Errors.raise_error uu____13353
                                         p.FStar_Syntax_Syntax.p
                                     else ());
                                    (let uu____13391 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____13391
                                     then
                                       let uu____13392 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____13392
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1,
                                       guard_pat_annots, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____13401 =
                   let uu____13408 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____13408
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____13401 with
                  | (scrutinee_env,uu____13440) ->
                      let uu____13445 = tc_pat true pat_t pattern in
                      (match uu____13445 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,guard_pat_annots,norm_pat_exp)
                           ->
                           let uu____13494 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____13516 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____13516
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____13530 =
                                      let uu____13537 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool in
                                      tc_term uu____13537 e in
                                    match uu____13530 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g)) in
                           (match uu____13494 with
                            | (when_clause1,g_when) ->
                                let uu____13579 = tc_term pat_env branch_exp in
                                (match uu____13579 with
                                 | (branch_exp1,c,g_branch) ->
                                     let g_branch1 =
                                       FStar_TypeChecker_Rel.conj_guard
                                         guard_pat_annots g_branch in
                                     let when_condition =
                                       match when_clause1 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some w ->
                                           let uu____13620 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_41  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_41) uu____13620 in
                                     let uu____13623 =
                                       let eqs =
                                         let uu____13641 =
                                           let uu____13642 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____13642 in
                                         if uu____13641
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____13649 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____13666 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____13667 ->
                                                FStar_Pervasives_Native.None
                                            | uu____13668 ->
                                                let uu____13669 =
                                                  let uu____13670 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____13670 pat_t
                                                    scrutinee_tm e in
                                                FStar_Pervasives_Native.Some
                                                  uu____13669) in
                                       let uu____13671 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch1 in
                                       match uu____13671 with
                                       | (c1,g_branch2) ->
                                           let uu____13694 =
                                             match (eqs, when_condition) with
                                             | uu____13707 when
                                                 let uu____13716 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation
                                                   uu____13716
                                                 -> (c1, g_when)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.None
                                                ) -> (c1, g_when)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.None
                                                ) ->
                                                 let gf =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf in
                                                 let uu____13728 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____13729 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____13728, uu____13729)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____13738 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____13738 in
                                                 let uu____13739 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____13740 =
                                                   let uu____13741 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____13741 g_when in
                                                 (uu____13739, uu____13740)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____13749 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____13749, g_when) in
                                           (match uu____13694 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let maybe_return_c_weak
                                                  should_return =
                                                  let c_weak1 =
                                                    let uu____13774 =
                                                      should_return &&
                                                        (FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                           c_weak) in
                                                    if uu____13774
                                                    then
                                                      FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                        env branch_exp1
                                                        c_weak
                                                    else c_weak in
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak1 in
                                                let uu____13776 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                ((c_weak.FStar_Syntax_Syntax.eff_name),
                                                  (c_weak.FStar_Syntax_Syntax.cflags),
                                                  maybe_return_c_weak,
                                                  uu____13776, g_branch2)) in
                                     (match uu____13623 with
                                      | (effect_label,cflags,maybe_return_c,g_when1,g_branch2)
                                          ->
                                          let branch_guard =
                                            let uu____13819 =
                                              let uu____13820 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____13820 in
                                            if uu____13819
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____13850 =
                                                     let uu____13851 =
                                                       let uu____13852 =
                                                         let uu____13855 =
                                                           let uu____13862 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____13862 in
                                                         FStar_Pervasives_Native.snd
                                                           uu____13855 in
                                                       FStar_List.length
                                                         uu____13852 in
                                                     uu____13851 >
                                                       (Prims.parse_int "1") in
                                                   if uu____13850
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____13868 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____13868 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____13889 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None in
                                                         let disc1 =
                                                           let uu____13904 =
                                                             let uu____13905
                                                               =
                                                               let uu____13906
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____13906] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____13905 in
                                                           uu____13904
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____13909 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool in
                                                         [uu____13909]
                                                   else [] in
                                                 let fail uu____13914 =
                                                   let uu____13915 =
                                                     let uu____13916 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____13917 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____13918 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____13916
                                                       uu____13917
                                                       uu____13918 in
                                                   failwith uu____13915 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____13929) ->
                                                       head_constructor t1
                                                   | uu____13934 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____13936 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____13936
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____13939 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____13956;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____13957;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____13958;_},uu____13959)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____13996 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c1 ->
                                                     let uu____13998 =
                                                       let uu____13999 =
                                                         tc_constant env
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c1 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____13999
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____13998]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____14000 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____14008 =
                                                       let uu____14009 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____14009 in
                                                     if uu____14008
                                                     then []
                                                     else
                                                       (let uu____14013 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____14013)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____14016 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____14018 =
                                                       let uu____14019 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____14019 in
                                                     if uu____14018
                                                     then []
                                                     else
                                                       (let uu____14023 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____14023)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____14049 =
                                                       let uu____14050 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____14050 in
                                                     if uu____14049
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____14057 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____14089
                                                                     ->
                                                                    match uu____14089
                                                                    with
                                                                    | 
                                                                    (ei,uu____14099)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____14105
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____14105
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____14126
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____14140
                                                                    =
                                                                    let uu____14141
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____14142
                                                                    =
                                                                    let uu____14143
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____14143] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____14141
                                                                    uu____14142 in
                                                                    uu____14140
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____14057
                                                            FStar_List.flatten in
                                                        let uu____14152 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____14152
                                                          sub_term_guards)
                                                 | uu____14155 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____14167 =
                                                   let uu____14168 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____14168 in
                                                 if uu____14167
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____14171 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____14171 in
                                                    let uu____14176 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____14176 with
                                                    | (k,uu____14182) ->
                                                        let uu____14183 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____14183
                                                         with
                                                         | (t1,uu____14191,uu____14192)
                                                             -> t1)) in
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
                                            FStar_TypeChecker_Rel.conj_guard
                                              g_when1 g_branch2 in
                                          ((let uu____14198 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____14198
                                            then
                                              let uu____14199 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____14199
                                            else ());
                                           (let uu____14201 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____14201, branch_guard,
                                              effect_label, cflags,
                                              maybe_return_c, guard)))))))))
and check_top_level_let:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let uu____14231 = check_let_bound_def true env1 lb in
          (match uu____14231 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____14253 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____14270 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____14270, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____14273 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____14273
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____14277 =
                      let uu____14290 =
                        let uu____14305 =
                          let uu____14314 =
                            let uu____14325 =
                              FStar_Syntax_Syntax.lcomp_comp c1 in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____14325) in
                          [uu____14314] in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____14305 in
                      FStar_List.hd uu____14290 in
                    match uu____14277 with
                    | (uu____14370,univs1,e11,c11,gvs) ->
                        let g12 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Rel.map_guard g11)
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta;
                               FStar_TypeChecker_Normalize.NoDeltaSteps;
                               FStar_TypeChecker_Normalize.CompressUvars;
                               FStar_TypeChecker_Normalize.NoFullNorm;
                               FStar_TypeChecker_Normalize.Exclude
                                 FStar_TypeChecker_Normalize.Zeta] env1) in
                        let g13 =
                          FStar_TypeChecker_Rel.abstract_guard_n gvs g12 in
                        let uu____14383 = FStar_Syntax_Util.lcomp_of_comp c11 in
                        (g13, e11, univs1, uu____14383)) in
               (match uu____14253 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____14394 =
                      let uu____14401 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____14401
                      then
                        let uu____14408 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____14408 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____14431 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.log_issue uu____14431
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____14432 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____14432, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____14442 =
                              FStar_Syntax_Syntax.lcomp_comp c11 in
                            FStar_All.pipe_right uu____14442
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm] env1) in
                          let e21 =
                            let uu____14446 =
                              FStar_Syntax_Util.is_pure_comp c in
                            if uu____14446
                            then e2
                            else
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta
                                   (e2,
                                     (FStar_Syntax_Syntax.Meta_desugared
                                        FStar_Syntax_Syntax.Masked_effect)))
                                FStar_Pervasives_Native.None
                                e2.FStar_Syntax_Syntax.pos in
                          (e21, c))) in
                    (match uu____14394 with
                     | (e21,c12) ->
                         let cres =
                           FStar_TypeChecker_Env.null_wp_for_eff env1
                             (FStar_Syntax_Util.comp_effect_name c12)
                             FStar_Syntax_Syntax.U_zero
                             FStar_Syntax_Syntax.t_unit in
                         let lb1 =
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             lb.FStar_Syntax_Syntax.lbname univ_vars2
                             (FStar_Syntax_Util.comp_result c12)
                             (FStar_Syntax_Util.comp_effect_name c12) e11 in
                         let uu____14470 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         let uu____14483 =
                           FStar_Syntax_Util.lcomp_of_comp cres in
                         (uu____14470, uu____14483,
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____14486 -> failwith "Impossible"
and check_inner_let:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let env2 =
            let uu___94_14517 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___94_14517.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___94_14517.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___94_14517.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___94_14517.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___94_14517.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___94_14517.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___94_14517.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___94_14517.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___94_14517.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___94_14517.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___94_14517.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___94_14517.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___94_14517.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___94_14517.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___94_14517.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___94_14517.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___94_14517.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___94_14517.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___94_14517.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___94_14517.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___94_14517.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___94_14517.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___94_14517.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___94_14517.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___94_14517.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___94_14517.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___94_14517.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___94_14517.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___94_14517.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___94_14517.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___94_14517.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___94_14517.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___94_14517.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___94_14517.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____14518 =
            let uu____14529 =
              let uu____14530 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____14530 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____14529 lb in
          (match uu____14518 with
           | (e1,uu____14552,c1,g1,annotated) ->
               let x =
                 let uu___95_14557 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___95_14557.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___95_14557.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____14558 =
                 let uu____14563 =
                   let uu____14564 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____14564] in
                 FStar_Syntax_Subst.open_term uu____14563 e2 in
               (match uu____14558 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = FStar_Pervasives_Native.fst xbinder in
                    let env_x = FStar_TypeChecker_Env.push_bv env2 x1 in
                    let uu____14584 = tc_term env_x e21 in
                    (match uu____14584 with
                     | (e22,c2,g2) ->
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
                             c1.FStar_Syntax_Syntax.eff_name e11 in
                         let e3 =
                           let uu____14609 =
                             let uu____14612 =
                               let uu____14613 =
                                 let uu____14626 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____14626) in
                               FStar_Syntax_Syntax.Tm_let uu____14613 in
                             FStar_Syntax_Syntax.mk uu____14612 in
                           uu____14609 FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____14640 =
                             let uu____14641 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____14642 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____14641
                               c1.FStar_Syntax_Syntax.res_typ uu____14642 e11 in
                           FStar_All.pipe_left
                             (fun _0_42  ->
                                FStar_TypeChecker_Common.NonTrivial _0_42)
                             uu____14640 in
                         let g21 =
                           let uu____14644 =
                             let uu____14645 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____14645 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____14644 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____14647 =
                           let uu____14648 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____14648 in
                         if uu____14647
                         then
                           let tt =
                             let uu____14658 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____14658
                               FStar_Option.get in
                           ((let uu____14664 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____14664
                             then
                               let uu____14665 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____14666 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____14665 uu____14666
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape FStar_Pervasives_Native.None
                                env2 [x1] cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____14671 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____14671
                             then
                               let uu____14672 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____14673 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____14672 uu____14673
                             else ());
                            (e4,
                              ((let uu___96_14676 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___96_14676.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___96_14676.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp_thunk =
                                    (uu___96_14676.FStar_Syntax_Syntax.comp_thunk)
                                })), guard)))))
      | uu____14677 -> failwith "Impossible"
and check_top_level_let_rec:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____14709 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____14709 with
           | (lbs1,e21) ->
               let uu____14728 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____14728 with
                | (env0,topt) ->
                    let uu____14747 = build_let_rec_env true env0 lbs1 in
                    (match uu____14747 with
                     | (lbs2,rec_env) ->
                         let uu____14766 = check_let_recs rec_env lbs2 in
                         (match uu____14766 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____14786 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____14786
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____14792 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____14792
                                  (fun _0_43  ->
                                     FStar_Pervasives_Native.Some _0_43) in
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
                                              lbdef))
                                else
                                  (let ecs =
                                     let uu____14841 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____14881 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____14881))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____14841 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____14930  ->
                                           match uu____14930 with
                                           | (x,uvs,e,c,gvs) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____14977 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____14977 in
                              let uu____14982 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                              (match uu____14982 with
                               | (lbs5,e22) ->
                                   ((let uu____15002 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1 in
                                     FStar_All.pipe_right uu____15002
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____15003 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     (uu____15003, cres,
                                       FStar_TypeChecker_Rel.trivial_guard))))))))
      | uu____15016 -> failwith "Impossible"
and check_inner_let_rec:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____15048 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____15048 with
           | (lbs1,e21) ->
               let uu____15067 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____15067 with
                | (env0,topt) ->
                    let uu____15086 = build_let_rec_env false env0 lbs1 in
                    (match uu____15086 with
                     | (lbs2,rec_env) ->
                         let uu____15105 = check_let_recs rec_env lbs2 in
                         (match uu____15105 with
                          | (lbs3,g_lbs) ->
                              let uu____15124 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___97_15147 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___97_15147.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___97_15147.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___98_15149 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___98_15149.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___98_15149.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___98_15149.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___98_15149.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____15124 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____15176 = tc_term env2 e21 in
                                   (match uu____15176 with
                                    | (e22,cres,g2) ->
                                        let cres1 =
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env2 e22 cres in
                                        let cres2 =
                                          FStar_Syntax_Util.lcomp_set_flags
                                            cres1
                                            [FStar_Syntax_Syntax.SHOULD_NOT_INLINE] in
                                        let guard =
                                          let uu____15195 =
                                            let uu____15196 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____15196 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____15195 in
                                        let cres3 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres2 in
                                        let tres =
                                          norm env2
                                            cres3.FStar_Syntax_Syntax.res_typ in
                                        let cres4 =
                                          let uu___99_15200 = cres3 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___99_15200.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___99_15200.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp_thunk =
                                              (uu___99_15200.FStar_Syntax_Syntax.comp_thunk)
                                          } in
                                        let uu____15201 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____15201 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____15237 ->
                                                  (e, cres4, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  let cres5 =
                                                    let uu___100_15242 =
                                                      cres4 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___100_15242.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___100_15242.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp_thunk
                                                        =
                                                        (uu___100_15242.FStar_Syntax_Syntax.comp_thunk)
                                                    } in
                                                  (e, cres5, guard)))))))))
      | uu____15245 -> failwith "Impossible"
and build_let_rec_env:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun top_level  ->
    fun env  ->
      fun lbs  ->
        let env0 = env in
        let termination_check_enabled lbname lbdef lbtyp =
          let uu____15274 = FStar_Options.ml_ish () in
          if uu____15274
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp in
             let uu____15277 = FStar_Syntax_Util.arrow_formals_comp t in
             match uu____15277 with
             | (formals,c) ->
                 let uu____15302 = FStar_Syntax_Util.abs_formals lbdef in
                 (match uu____15302 with
                  | (actuals,uu____15312,uu____15313) ->
                      if
                        ((FStar_List.length formals) < (Prims.parse_int "1"))
                          ||
                          ((FStar_List.length actuals) <
                             (Prims.parse_int "1"))
                      then
                        let uu____15326 =
                          let uu____15331 =
                            let uu____15332 =
                              FStar_Syntax_Print.term_to_string lbdef in
                            let uu____15333 =
                              FStar_Syntax_Print.term_to_string lbtyp in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____15332 uu____15333 in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____15331) in
                        FStar_Errors.raise_error uu____15326
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____15336 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____15336 actuals in
                         if
                           (FStar_List.length formals) <>
                             (FStar_List.length actuals1)
                         then
                           (let actuals_msg =
                              let n1 = FStar_List.length actuals1 in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument was found"
                              else
                                (let uu____15357 =
                                   FStar_Util.string_of_int n1 in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____15357) in
                            let formals_msg =
                              let n1 = FStar_List.length formals in
                              if n1 = (Prims.parse_int "1")
                              then "1 argument"
                              else
                                (let uu____15375 =
                                   FStar_Util.string_of_int n1 in
                                 FStar_Util.format1 "%s arguments"
                                   uu____15375) in
                            let msg =
                              let uu____15383 =
                                FStar_Syntax_Print.term_to_string lbtyp in
                              let uu____15384 =
                                FStar_Syntax_Print.lbname_to_string lbname in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____15383 uu____15384 formals_msg
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
        let uu____15391 =
          FStar_List.fold_left
            (fun uu____15417  ->
               fun lb  ->
                 match uu____15417 with
                 | (lbs1,env1) ->
                     let uu____15437 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____15437 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1 in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef in
                          let t1 =
                            if Prims.op_Negation check_t
                            then t
                            else
                              (let uu____15457 =
                                 let uu____15464 =
                                   let uu____15465 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____15465 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___101_15476 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___101_15476.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___101_15476.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___101_15476.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___101_15476.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___101_15476.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___101_15476.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___101_15476.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___101_15476.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___101_15476.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___101_15476.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___101_15476.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___101_15476.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___101_15476.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___101_15476.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___101_15476.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___101_15476.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___101_15476.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___101_15476.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___101_15476.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___101_15476.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___101_15476.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___101_15476.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___101_15476.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___101_15476.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___101_15476.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___101_15476.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___101_15476.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___101_15476.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___101_15476.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___101_15476.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___101_15476.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___101_15476.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___101_15476.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___101_15476.FStar_TypeChecker_Env.dep_graph)
                                    }) t uu____15464 in
                               match uu____15457 with
                               | (t1,uu____15478,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____15482 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____15482);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____15484 =
                              termination_check_enabled
                                lb.FStar_Syntax_Syntax.lbname e t1 in
                            if uu____15484
                            then
                              let uu___102_15485 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___102_15485.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___102_15485.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___102_15485.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___102_15485.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___102_15485.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___102_15485.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___102_15485.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___102_15485.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___102_15485.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___102_15485.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___102_15485.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___102_15485.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1,
                                     univ_vars1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___102_15485.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___102_15485.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___102_15485.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___102_15485.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___102_15485.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___102_15485.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___102_15485.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___102_15485.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___102_15485.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___102_15485.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___102_15485.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___102_15485.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___102_15485.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___102_15485.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___102_15485.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___102_15485.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___102_15485.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___102_15485.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___102_15485.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___102_15485.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___102_15485.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___102_15485.FStar_TypeChecker_Env.dep_graph)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname
                                (univ_vars1, t1) in
                          let lb1 =
                            let uu___103_15502 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___103_15502.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___103_15502.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____15391 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lbs  ->
      let uu____15525 =
        let uu____15534 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____15560 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef in
                  match uu____15560 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____15588 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____15588
                       | uu____15593 ->
                           let lb1 =
                             let uu___104_15596 = lb in
                             let uu____15597 =
                               FStar_Syntax_Util.abs bs t lcomp in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___104_15596.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___104_15596.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___104_15596.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___104_15596.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____15597
                             } in
                           let uu____15600 =
                             let uu____15607 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp in
                             tc_tot_or_gtot_term uu____15607
                               lb1.FStar_Syntax_Syntax.lbdef in
                           (match uu____15600 with
                            | (e,c,g) ->
                                ((let uu____15616 =
                                    let uu____15617 =
                                      FStar_Syntax_Util.is_total_lcomp c in
                                    Prims.op_Negation uu____15617 in
                                  if uu____15616
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
                                      FStar_Parser_Const.effect_Tot_lid e in
                                  (lb2, g))))))) in
        FStar_All.pipe_right uu____15534 FStar_List.unzip in
      match uu____15525 with
      | (lbs1,gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs
              FStar_TypeChecker_Rel.trivial_guard in
          (lbs1, g_lbs)
and check_let_bound_def:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.lcomp,
          FStar_TypeChecker_Env.guard_t,Prims.bool)
          FStar_Pervasives_Native.tuple5
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let uu____15666 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____15666 with
        | (env1,uu____15684) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____15692 = check_lbtyp top_level env lb in
            (match uu____15692 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____15736 =
                     tc_maybe_toplevel_term
                       (let uu___105_15745 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___105_15745.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___105_15745.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___105_15745.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___105_15745.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___105_15745.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___105_15745.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___105_15745.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___105_15745.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___105_15745.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___105_15745.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___105_15745.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___105_15745.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___105_15745.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___105_15745.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___105_15745.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___105_15745.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___105_15745.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___105_15745.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___105_15745.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.failhard =
                            (uu___105_15745.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___105_15745.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___105_15745.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___105_15745.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___105_15745.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___105_15745.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___105_15745.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___105_15745.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___105_15745.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___105_15745.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___105_15745.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___105_15745.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___105_15745.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___105_15745.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___105_15745.FStar_TypeChecker_Env.dep_graph)
                        }) e11 in
                   match uu____15736 with
                   | (e12,c1,g1) ->
                       let uu____15759 =
                         let uu____15764 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____15768  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____15764 e12 c1 wf_annot in
                       (match uu____15759 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____15783 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____15783
                              then
                                let uu____15784 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____15785 =
                                  FStar_Syntax_Print.lcomp_to_string c11 in
                                let uu____15786 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____15784 uu____15785 uu____15786
                              else ());
                             (e12, univ_vars1, c11, g11,
                               (FStar_Option.isSome topt)))))))
and check_lbtyp:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,FStar_TypeChecker_Env.guard_t,
          FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.subst_elt
                                           Prims.list,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple5
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let t = FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____15820 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____15820 with
             | (univ_opening,univ_vars1) ->
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                   univ_opening, env))
        | uu____15859 ->
            let uu____15860 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____15860 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____15909 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____15909)
                 else
                   (let uu____15917 = FStar_Syntax_Util.type_u () in
                    match uu____15917 with
                    | (k,uu____15937) ->
                        let uu____15938 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____15938 with
                         | (t2,uu____15960,g) ->
                             ((let uu____15963 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____15963
                               then
                                 let uu____15964 =
                                   let uu____15965 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____15965 in
                                 let uu____15966 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____15964 uu____15966
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____15969 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____15969))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun uu____15977  ->
      match uu____15977 with
      | (x,imp) ->
          let uu____15996 = FStar_Syntax_Util.type_u () in
          (match uu____15996 with
           | (tu,u) ->
               ((let uu____16016 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____16016
                 then
                   let uu____16017 = FStar_Syntax_Print.bv_to_string x in
                   let uu____16018 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____16019 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____16017 uu____16018 uu____16019
                 else ());
                (let uu____16021 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____16021 with
                 | (t,uu____16041,g) ->
                     let x1 =
                       ((let uu___106_16049 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___106_16049.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___106_16049.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____16051 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____16051
                       then
                         let uu____16052 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1) in
                         let uu____16053 =
                           FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____16052 uu____16053
                       else ());
                      (let uu____16055 = push_binding env x1 in
                       (x1, uu____16055, g, u))))))
and tc_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universes) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun bs  ->
      let rec aux env1 bs1 =
        match bs1 with
        | [] -> ([], env1, FStar_TypeChecker_Rel.trivial_guard, [])
        | b::bs2 ->
            let uu____16145 = tc_binder env1 b in
            (match uu____16145 with
             | (b1,env',g,u) ->
                 let uu____16186 = aux env' bs2 in
                 (match uu____16186 with
                  | (bs3,env'1,g',us) ->
                      let uu____16239 =
                        let uu____16240 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____16240 in
                      ((b1 :: bs3), env'1, uu____16239, (u :: us)))) in
      aux env bs
and tc_pats:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2 Prims.list Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pats  ->
      let tc_args env1 args =
        FStar_List.fold_right
          (fun uu____16325  ->
             fun uu____16326  ->
               match (uu____16325, uu____16326) with
               | ((t,imp),(args1,g)) ->
                   let uu____16395 = tc_term env1 t in
                   (match uu____16395 with
                    | (t1,uu____16413,g') ->
                        let uu____16415 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____16415))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____16457  ->
             match uu____16457 with
             | (pats1,g) ->
                 let uu____16482 = tc_args env p in
                 (match uu____16482 with
                  | (args,g') ->
                      let uu____16495 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____16495))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let uu____16508 = tc_maybe_toplevel_term env e in
      match uu____16508 with
      | (e1,c,g) ->
          let uu____16524 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____16524
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = FStar_Syntax_Syntax.lcomp_comp c in
             let c2 = norm_c env c1 in
             let uu____16535 =
               let uu____16540 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____16540
               then
                 let uu____16545 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____16545, false)
               else
                 (let uu____16547 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____16547, true)) in
             match uu____16535 with
             | (target_comp,allow_ghost) ->
                 let uu____16556 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____16556 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____16566 =
                        FStar_Syntax_Util.lcomp_of_comp target_comp in
                      let uu____16567 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, uu____16566, uu____16567)
                  | uu____16568 ->
                      if allow_ghost
                      then
                        let uu____16577 =
                          FStar_TypeChecker_Err.expected_ghost_expression e1
                            c2 in
                        FStar_Errors.raise_error uu____16577
                          e1.FStar_Syntax_Syntax.pos
                      else
                        (let uu____16589 =
                           FStar_TypeChecker_Err.expected_pure_expression e1
                             c2 in
                         FStar_Errors.raise_error uu____16589
                           e1.FStar_Syntax_Syntax.pos)))
and tc_check_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let env1 = FStar_TypeChecker_Env.set_expected_typ env t in
        tc_tot_or_gtot_term env1 e
and tc_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____16612 = tc_tot_or_gtot_term env t in
      match uu____16612 with
      | (t1,c,g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))
let type_of_tot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      (let uu____16640 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____16640
       then
         let uu____16641 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____16641
       else ());
      (let env1 =
         let uu___107_16644 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___107_16644.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___107_16644.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___107_16644.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___107_16644.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___107_16644.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___107_16644.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___107_16644.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___107_16644.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___107_16644.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___107_16644.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___107_16644.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___107_16644.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___107_16644.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___107_16644.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___107_16644.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___107_16644.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___107_16644.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___107_16644.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___107_16644.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___107_16644.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___107_16644.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___107_16644.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___107_16644.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___107_16644.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___107_16644.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___107_16644.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___107_16644.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___107_16644.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___107_16644.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___107_16644.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___107_16644.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___107_16644.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___107_16644.FStar_TypeChecker_Env.dep_graph)
         } in
       let uu____16651 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (e1,msg,uu____16686) ->
             let uu____16687 = FStar_TypeChecker_Env.get_range env1 in
             FStar_Errors.raise_error (e1, msg) uu____16687 in
       match uu____16651 with
       | (t,c,g) ->
           let uu____16703 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____16703
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____16713 =
                let uu____16718 =
                  let uu____16719 = FStar_Syntax_Print.term_to_string e in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____16719 in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____16718) in
              let uu____16720 = FStar_TypeChecker_Env.get_range env1 in
              FStar_Errors.raise_error uu____16713 uu____16720))
let level_of_type_fail:
  'Auu____16731 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____16731
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____16744 =
          let uu____16749 =
            let uu____16750 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____16750 t in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____16749) in
        let uu____16751 = FStar_TypeChecker_Env.get_range env in
        FStar_Errors.raise_error uu____16744 uu____16751
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____16768 =
            let uu____16769 = FStar_Syntax_Util.unrefine t1 in
            uu____16769.FStar_Syntax_Syntax.n in
          match uu____16768 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____16773 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____16776 = FStar_Syntax_Util.type_u () in
                 match uu____16776 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___110_16784 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___110_16784.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___110_16784.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___110_16784.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___110_16784.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___110_16784.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___110_16784.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___110_16784.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___110_16784.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___110_16784.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___110_16784.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___110_16784.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___110_16784.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___110_16784.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___110_16784.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___110_16784.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___110_16784.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___110_16784.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___110_16784.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___110_16784.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___110_16784.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___110_16784.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___110_16784.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___110_16784.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___110_16784.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___110_16784.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___110_16784.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___110_16784.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___110_16784.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___110_16784.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___110_16784.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___110_16784.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___110_16784.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___110_16784.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___110_16784.FStar_TypeChecker_Env.dep_graph)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____16788 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____16788
                       | uu____16789 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u)) in
        aux true t
let rec universe_of_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun e  ->
      let uu____16798 =
        let uu____16799 = FStar_Syntax_Subst.compress e in
        uu____16799.FStar_Syntax_Syntax.n in
      match uu____16798 with
      | FStar_Syntax_Syntax.Tm_bvar uu____16804 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____16809 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____16836 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____16852) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____16875,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____16902) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____16909 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____16909 with | ((uu____16920,t),uu____16922) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16927,(FStar_Util.Inl t,uu____16929),uu____16930) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16977,(FStar_Util.Inr c,uu____16979),uu____16980) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____17030;
             FStar_Syntax_Syntax.vars = uu____17031;_},us)
          ->
          let uu____17037 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____17037 with
           | ((us',t),uu____17050) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____17056 = FStar_TypeChecker_Env.get_range env in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____17056)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____17072 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____17073 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____17083) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____17106 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____17106 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____17126  ->
                      match uu____17126 with
                      | (b,uu____17132) ->
                          let uu____17133 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____17133) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____17138 = universe_of_aux env res in
                 level_of_type env res uu____17138 in
               let u_c =
                 let uu____17140 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____17140 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____17144 = universe_of_aux env trepr in
                     level_of_type env trepr uu____17144 in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us)) in
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
                 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rec type_of_head retry hd2 args1 =
            let hd3 = FStar_Syntax_Subst.compress hd2 in
            match hd3.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____17237 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____17252 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____17291 ->
                let uu____17292 = universe_of_aux env hd3 in
                (uu____17292, args1)
            | FStar_Syntax_Syntax.Tm_name uu____17305 ->
                let uu____17306 = universe_of_aux env hd3 in
                (uu____17306, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____17319 ->
                let uu____17336 = universe_of_aux env hd3 in
                (uu____17336, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____17349 ->
                let uu____17356 = universe_of_aux env hd3 in
                (uu____17356, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____17369 ->
                let uu____17396 = universe_of_aux env hd3 in
                (uu____17396, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____17409 ->
                let uu____17416 = universe_of_aux env hd3 in
                (uu____17416, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____17429 ->
                let uu____17430 = universe_of_aux env hd3 in
                (uu____17430, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____17443 ->
                let uu____17456 = universe_of_aux env hd3 in
                (uu____17456, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____17469 ->
                let uu____17476 = universe_of_aux env hd3 in
                (uu____17476, args1)
            | FStar_Syntax_Syntax.Tm_type uu____17489 ->
                let uu____17490 = universe_of_aux env hd3 in
                (uu____17490, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____17503,hd4::uu____17505) ->
                let uu____17570 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____17570 with
                 | (uu____17585,uu____17586,hd5) ->
                     let uu____17604 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____17604 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____17655 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____17657 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____17657 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____17708 ->
                let uu____17709 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____17709 with
                 | (env1,uu____17731) ->
                     let env2 =
                       let uu___111_17737 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___111_17737.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___111_17737.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___111_17737.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___111_17737.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___111_17737.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___111_17737.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___111_17737.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___111_17737.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___111_17737.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___111_17737.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___111_17737.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___111_17737.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___111_17737.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___111_17737.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___111_17737.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___111_17737.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___111_17737.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___111_17737.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___111_17737.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___111_17737.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___111_17737.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___111_17737.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___111_17737.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___111_17737.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___111_17737.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___111_17737.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___111_17737.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___111_17737.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___111_17737.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___111_17737.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___111_17737.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___111_17737.FStar_TypeChecker_Env.dep_graph)
                       } in
                     ((let uu____17739 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____17739
                       then
                         let uu____17740 =
                           let uu____17741 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____17741 in
                         let uu____17742 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____17740 uu____17742
                       else ());
                      (let uu____17744 = tc_term env2 hd3 in
                       match uu____17744 with
                       | (uu____17765,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____17766;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____17768;
                                        FStar_Syntax_Syntax.comp_thunk =
                                          uu____17769;_},g)
                           ->
                           ((let uu____17788 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____17788
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____17799 = type_of_head true hd1 args in
          (match uu____17799 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____17839 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____17839 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____17883 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____17883)))
      | FStar_Syntax_Syntax.Tm_match (uu____17886,hd1::uu____17888) ->
          let uu____17953 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____17953 with
           | (uu____17956,uu____17957,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____17975,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____18018 = universe_of_aux env e in
      level_of_type env e uu____18018
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tps  ->
      let uu____18037 = tc_binders env tps in
      match uu____18037 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))
let rec type_of_well_typed_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let mk_tm_type u =
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
          FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
      let uu____18081 =
        let uu____18082 = FStar_Syntax_Subst.compress t in
        uu____18082.FStar_Syntax_Syntax.n in
      match uu____18081 with
      | FStar_Syntax_Syntax.Tm_delayed uu____18087 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____18114 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____18118 = x.FStar_Syntax_Syntax.sort in
          FStar_Pervasives_Native.Some uu____18118
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____18125 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_Util.bind_opt uu____18125
            (fun uu____18139  ->
               match uu____18139 with
               | (t1,uu____18147) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____18149;
             FStar_Syntax_Syntax.vars = uu____18150;_},us)
          ->
          let uu____18156 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_Util.bind_opt uu____18156
            (fun uu____18170  ->
               match uu____18170 with
               | (t1,uu____18178) -> FStar_Pervasives_Native.Some t1)
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____18180 = tc_constant env t.FStar_Syntax_Syntax.pos sc in
          FStar_Pervasives_Native.Some uu____18180
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____18182 = mk_tm_type (FStar_Syntax_Syntax.U_succ u) in
          FStar_Pervasives_Native.Some uu____18182
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____18191;_})
          ->
          let mk_comp =
            if FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              if
                FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid
              then
                FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
              else FStar_Pervasives_Native.None in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____18278 = universe_of_well_typed_term env tbody in
               FStar_Util.bind_opt uu____18278
                 (fun u  ->
                    let uu____18286 =
                      let uu____18289 =
                        let uu____18292 =
                          let uu____18293 =
                            let uu____18306 =
                              f tbody (FStar_Pervasives_Native.Some u) in
                            (bs, uu____18306) in
                          FStar_Syntax_Syntax.Tm_arrow uu____18293 in
                        FStar_Syntax_Syntax.mk uu____18292 in
                      uu____18289 FStar_Pervasives_Native.None
                        t.FStar_Syntax_Syntax.pos in
                    FStar_Pervasives_Native.Some uu____18286))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____18336 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____18336 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____18383 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1) in
                     FStar_Util.bind_opt uu____18383
                       (fun uc  ->
                          let uu____18391 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us)) in
                          FStar_Pervasives_Native.Some uu____18391)
                 | (x,imp)::bs3 ->
                     let uu____18409 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort in
                     FStar_Util.bind_opt uu____18409
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x in
                          aux env2 (u_x :: us) bs3) in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____18418 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____18436) ->
          let uu____18441 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort in
          FStar_Util.bind_opt uu____18441
            (fun u_x  ->
               let uu____18449 = mk_tm_type u_x in
               FStar_Pervasives_Native.Some uu____18449)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1 in
          let rec aux t_hd1 =
            let uu____18485 =
              let uu____18486 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1 in
              uu____18486.FStar_Syntax_Syntax.n in
            match uu____18485 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args in
                let n_bs = FStar_List.length bs in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____18548 = FStar_Util.first_N n_args bs in
                    match uu____18548 with
                    | (bs1,rest) ->
                        let t1 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos in
                        let uu____18618 =
                          let uu____18623 = FStar_Syntax_Syntax.mk_Total t1 in
                          FStar_Syntax_Subst.open_comp bs1 uu____18623 in
                        (match uu____18618 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____18659 = FStar_Syntax_Subst.open_comp bs c in
                       match uu____18659 with
                       | (bs1,c1) ->
                           let uu____18674 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1 in
                           if uu____18674
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____18716  ->
                     match uu____18716 with
                     | (bs1,t1) ->
                         let subst1 =
                           FStar_List.map2
                             (fun b  ->
                                fun a  ->
                                  FStar_Syntax_Syntax.NT
                                    ((FStar_Pervasives_Native.fst b),
                                      (FStar_Pervasives_Native.fst a))) bs1
                             args in
                         let uu____18762 = FStar_Syntax_Subst.subst subst1 t1 in
                         FStar_Pervasives_Native.Some uu____18762)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____18764) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____18770,uu____18771) ->
                aux t1
            | uu____18812 -> FStar_Pervasives_Native.None in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____18813,(FStar_Util.Inl t1,uu____18815),uu____18816) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____18865,(FStar_Util.Inr c,uu____18867),uu____18868) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (uu____18917,t1) ->
          FStar_Pervasives_Native.Some t1
      | FStar_Syntax_Syntax.Tm_meta (t1,uu____18946) ->
          type_of_well_typed_term env t1
      | FStar_Syntax_Syntax.Tm_match uu____18951 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____18974 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____18987 ->
          FStar_Pervasives_Native.None
and universe_of_well_typed_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____18998 = type_of_well_typed_term env t in
      match uu____18998 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____19004;
            FStar_Syntax_Syntax.vars = uu____19005;_}
          -> FStar_Pervasives_Native.Some u
      | uu____19010 -> FStar_Pervasives_Native.None
let check_type_of_well_typed_term:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun must_total  ->
    fun env  ->
      fun t  ->
        fun k  ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k in
          let env2 =
            let uu___112_19027 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___112_19027.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___112_19027.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___112_19027.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___112_19027.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___112_19027.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___112_19027.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___112_19027.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___112_19027.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___112_19027.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___112_19027.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___112_19027.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___112_19027.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___112_19027.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___112_19027.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___112_19027.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___112_19027.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___112_19027.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___112_19027.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___112_19027.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___112_19027.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___112_19027.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___112_19027.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___112_19027.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___112_19027.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___112_19027.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___112_19027.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qname_and_index =
                (uu___112_19027.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___112_19027.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___112_19027.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___112_19027.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___112_19027.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___112_19027.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___112_19027.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___112_19027.FStar_TypeChecker_Env.dep_graph)
            } in
          let slow_check uu____19031 =
            if must_total
            then
              let uu____19032 = env2.FStar_TypeChecker_Env.type_of env2 t in
              match uu____19032 with | (uu____19039,uu____19040,g) -> g
            else
              (let uu____19043 = env2.FStar_TypeChecker_Env.tc_term env2 t in
               match uu____19043 with | (uu____19050,uu____19051,g) -> g) in
          let uu____19053 = type_of_well_typed_term env2 t in
          match uu____19053 with
          | FStar_Pervasives_Native.None  -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              let uu____19057 =
                value_check_expected_typ env2 t (FStar_Util.Inl k')
                  FStar_TypeChecker_Rel.trivial_guard in
              (match uu____19057 with
               | (uu____19064,uu____19065,g) ->
                   let uu____19067 = FStar_TypeChecker_Rel.is_trivial g in
                   if uu____19067 then g else slow_check ())
