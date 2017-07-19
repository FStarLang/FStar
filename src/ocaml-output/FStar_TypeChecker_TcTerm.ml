open Prims
let instantiate_both: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___89_5 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___89_5.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___89_5.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___89_5.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___89_5.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___89_5.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___89_5.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___89_5.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___89_5.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___89_5.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___89_5.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___89_5.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___89_5.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___89_5.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___89_5.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___89_5.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___89_5.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___89_5.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___89_5.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___89_5.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___89_5.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___89_5.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___89_5.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___89_5.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___89_5.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___89_5.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___89_5.FStar_TypeChecker_Env.is_native_tactic)
    }
let no_inst: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___90_10 = env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___90_10.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___90_10.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___90_10.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___90_10.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___90_10.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___90_10.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___90_10.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___90_10.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___90_10.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___90_10.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___90_10.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___90_10.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___90_10.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___90_10.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___90_10.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___90_10.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___90_10.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___90_10.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___90_10.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___90_10.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___90_10.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___90_10.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___90_10.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___90_10.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___90_10.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___90_10.FStar_TypeChecker_Env.is_native_tactic)
    }
let mk_lex_list:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
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
           let uu____57 =
             let uu____58 =
               let uu____59 = FStar_Syntax_Syntax.as_arg v1 in
               let uu____60 =
                 let uu____63 = FStar_Syntax_Syntax.as_arg tl1 in [uu____63] in
               uu____59 :: uu____60 in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____58 in
           uu____57
             (FStar_Pervasives_Native.Some
                (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r) vs
      FStar_Syntax_Util.lex_top
let is_eq:
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___84_71  ->
    match uu___84_71 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____74 -> false
let steps env =
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
            | uu____135 ->
                let t1 = if try_norm then norm env t else t in
                let fvs' = FStar_Syntax_Free.names t1 in
                let uu____143 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs in
                (match uu____143 with
                 | FStar_Pervasives_Native.None  -> t1
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____153 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____155 =
                                  FStar_Syntax_Print.bv_to_string x in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____155
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____157 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____158 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1 in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____157 uu____158 in
                          let uu____159 =
                            let uu____160 =
                              let uu____165 =
                                FStar_TypeChecker_Env.get_range env in
                              (msg, uu____165) in
                            FStar_Errors.Error uu____160 in
                          raise uu____159 in
                        let s =
                          let uu____167 =
                            let uu____168 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____168 in
                          FStar_TypeChecker_Util.new_uvar env uu____167 in
                        let uu____177 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s in
                        match uu____177 with
                        | FStar_Pervasives_Native.Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____182 -> fail ())) in
          aux false kt
let push_binding env b =
  FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
let maybe_extend_subst:
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.binder ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.subst_t
  =
  fun s  ->
    fun b  ->
      fun v1  ->
        let uu____228 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____228
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v1))
          :: s
let set_lcomp_result:
  FStar_Syntax_Syntax.lcomp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___91_250 = lc in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___91_250.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___91_250.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____253  ->
             let uu____254 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Util.set_result_typ uu____254 t)
      }
let memo_tk:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun t  ->
      FStar_ST.write e.FStar_Syntax_Syntax.tk
        (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.n));
      e
let value_check_expected_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp) FStar_Util.either
        ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun tlc  ->
        fun guard  ->
          let should_return t =
            let uu____310 =
              let uu____311 = FStar_Syntax_Subst.compress t in
              uu____311.FStar_Syntax_Syntax.n in
            match uu____310 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____316,c) ->
                let uu____338 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c) in
                if uu____338
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c) in
                  let uu____340 =
                    let uu____341 = FStar_Syntax_Subst.compress t1 in
                    uu____341.FStar_Syntax_Syntax.n in
                  (match uu____340 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____347 -> false
                   | uu____348 -> true)
                else false
            | uu____350 -> true in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____353 =
                  let uu____358 =
                    (let uu____361 = should_return t in
                     Prims.op_Negation uu____361) ||
                      (let uu____363 =
                         FStar_TypeChecker_Env.should_verify env in
                       Prims.op_Negation uu____363) in
                  if uu____358
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e in
                FStar_Syntax_Util.lcomp_of_comp uu____353
            | FStar_Util.Inr lc -> lc in
          let t = lc.FStar_Syntax_Syntax.res_typ in
          let uu____375 =
            let uu____382 = FStar_TypeChecker_Env.expected_typ env in
            match uu____382 with
            | FStar_Pervasives_Native.None  ->
                let uu____391 = memo_tk e t in (uu____391, lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                ((let uu____394 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High in
                  if uu____394
                  then
                    let uu____395 = FStar_Syntax_Print.term_to_string t in
                    let uu____396 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____395
                      uu____396
                  else ());
                 (let uu____398 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t' in
                  match uu____398 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____416 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____416 with
                       | (e2,g) ->
                           ((let uu____430 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____430
                             then
                               let uu____431 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____432 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____433 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____434 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____431 uu____432 uu____433 uu____434
                             else ());
                            (let msg =
                               let uu____441 =
                                 FStar_TypeChecker_Rel.is_trivial g in
                               if uu____441
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_39  ->
                                      FStar_Pervasives_Native.Some _0_39)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             let uu____458 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1 in
                             match uu____458 with
                             | (lc2,g2) ->
                                 let uu____471 = memo_tk e2 t' in
                                 (uu____471, (set_lcomp_result lc2 t'), g2)))))) in
          match uu____375 with
          | (e1,lc1,g) ->
              ((let uu____482 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low in
                if uu____482
                then
                  let uu____483 = FStar_Syntax_Print.lcomp_to_string lc1 in
                  FStar_Util.print1 "Return comp type is %s\n" uu____483
                else ());
               (e1, lc1, g))
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
        let uu____509 = FStar_TypeChecker_Env.expected_typ env in
        match uu____509 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____519 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____519 with
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
      fun uu____555  ->
        match uu____555 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____588 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____588
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____590 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____590
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____592 =
              match copt with
              | FStar_Pervasives_Native.Some uu____605 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____608 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____610 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____610)) in
                  if uu____608
                  then
                    let uu____617 =
                      let uu____620 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos in
                      FStar_Pervasives_Native.Some uu____620 in
                    (uu____617, c)
                  else
                    (let uu____624 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____624
                     then
                       let uu____631 = tot_or_gtot c in
                       (FStar_Pervasives_Native.None, uu____631)
                     else
                       (let uu____635 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____635
                        then
                          let uu____642 =
                            let uu____645 = tot_or_gtot c in
                            FStar_Pervasives_Native.Some uu____645 in
                          (uu____642, c)
                        else (FStar_Pervasives_Native.None, c))) in
            (match uu____592 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let uu____671 =
                        FStar_TypeChecker_Util.check_comp env e c2 expected_c in
                      (match uu____671 with
                       | (e1,uu____685,g) ->
                           let g1 =
                             let uu____688 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_TypeChecker_Util.label_guard uu____688
                               "could not prove post-condition" g in
                           ((let uu____690 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low in
                             if uu____690
                             then
                               let uu____691 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos in
                               let uu____692 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1 in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____691 uu____692
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c2)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c2) in
                             (e2, expected_c, g1))))))
let no_logical_guard env uu____724 =
  match uu____724 with
  | (te,kt,f) ->
      let uu____734 = FStar_TypeChecker_Rel.guard_form f in
      (match uu____734 with
       | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
       | FStar_TypeChecker_Common.NonTrivial f1 ->
           let uu____742 =
             let uu____743 =
               let uu____748 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1 in
               let uu____749 = FStar_TypeChecker_Env.get_range env in
               (uu____748, uu____749) in
             FStar_Errors.Error uu____743 in
           raise uu____742)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____760 = FStar_TypeChecker_Env.expected_typ env in
    match uu____760 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None"
    | FStar_Pervasives_Native.Some t ->
        let uu____764 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____764
let check_smt_pat env t bs c =
  let uu____815 = FStar_Syntax_Util.is_smt_lemma t in
  if uu____815
  then
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp
        { FStar_Syntax_Syntax.comp_univs = uu____816;
          FStar_Syntax_Syntax.effect_name = uu____817;
          FStar_Syntax_Syntax.result_typ = uu____818;
          FStar_Syntax_Syntax.effect_args = _pre::_post::(pats,uu____822)::[];
          FStar_Syntax_Syntax.flags = uu____823;_}
        ->
        let pat_vars =
          let uu____889 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta] env pats in
          FStar_Syntax_Free.names uu____889 in
        let uu____890 =
          FStar_All.pipe_right bs
            (FStar_Util.find_opt
               (fun uu____917  ->
                  match uu____917 with
                  | (b,uu____923) ->
                      let uu____924 = FStar_Util.set_mem b pat_vars in
                      Prims.op_Negation uu____924)) in
        (match uu____890 with
         | FStar_Pervasives_Native.None  -> ()
         | FStar_Pervasives_Native.Some (x,uu____930) ->
             let uu____935 =
               let uu____936 = FStar_Syntax_Print.bv_to_string x in
               FStar_Util.format1
                 "Pattern misses at least one bound variable: %s" uu____936 in
             FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____935)
    | uu____937 -> failwith "Impossible"
  else ()
let guard_letrecs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        let uu____971 =
          let uu____972 = FStar_TypeChecker_Env.should_verify env in
          Prims.op_Negation uu____972 in
        if uu____971
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env in
               let env1 =
                 let uu___92_1003 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___92_1003.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___92_1003.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___92_1003.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___92_1003.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___92_1003.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___92_1003.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___92_1003.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___92_1003.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___92_1003.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___92_1003.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___92_1003.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___92_1003.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___92_1003.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___92_1003.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___92_1003.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___92_1003.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___92_1003.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___92_1003.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___92_1003.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___92_1003.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___92_1003.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___92_1003.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___92_1003.FStar_TypeChecker_Env.qname_and_index);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___92_1003.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth =
                     (uu___92_1003.FStar_TypeChecker_Env.synth);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___92_1003.FStar_TypeChecker_Env.is_native_tactic)
                 } in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Parser_Const.precedes_lid in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____1041  ->
                           match uu____1041 with
                           | (b,uu____1049) ->
                               let t =
                                 let uu____1051 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort in
                                 FStar_TypeChecker_Normalize.unfold_whnf env1
                                   uu____1051 in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type uu____1054 ->
                                    []
                                | FStar_Syntax_Syntax.Tm_arrow uu____1055 ->
                                    []
                                | uu____1070 ->
                                    let uu____1071 =
                                      FStar_Syntax_Syntax.bv_to_name b in
                                    [uu____1071]))) in
                 let as_lex_list dec =
                   let uu____1076 = FStar_Syntax_Util.head_and_args dec in
                   match uu____1076 with
                   | (head1,uu____1096) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.lexcons_lid
                            -> dec
                        | uu____1126 -> mk_lex_list [dec]) in
                 let cflags = FStar_Syntax_Util.comp_flags c in
                 let uu____1130 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___85_1139  ->
                           match uu___85_1139 with
                           | FStar_Syntax_Syntax.DECREASES uu____1140 -> true
                           | uu____1145 -> false)) in
                 match uu____1130 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.DECREASES dec) -> as_lex_list dec
                 | uu____1151 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions in
                     (match xs with
                      | x::[] -> x
                      | uu____1160 -> mk_lex_list xs) in
               let previous_dec = decreases_clause actuals expected_c in
               let guard_one_letrec uu____1179 =
                 match uu____1179 with
                 | (l,t) ->
                     let uu____1194 =
                       let uu____1195 = FStar_Syntax_Subst.compress t in
                       uu____1195.FStar_Syntax_Syntax.n in
                     (match uu____1194 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____1262  ->
                                    match uu____1262 with
                                    | (x,imp) ->
                                        let uu____1273 =
                                          FStar_Syntax_Syntax.is_null_bv x in
                                        if uu____1273
                                        then
                                          let uu____1278 =
                                            let uu____1279 =
                                              let uu____1282 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x in
                                              FStar_Pervasives_Native.Some
                                                uu____1282 in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____1279
                                              x.FStar_Syntax_Syntax.sort in
                                          (uu____1278, imp)
                                        else (x, imp))) in
                          let uu____1284 =
                            FStar_Syntax_Subst.open_comp formals1 c in
                          (match uu____1284 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1 in
                               let precedes1 =
                                 let uu____1305 =
                                   let uu____1306 =
                                     let uu____1307 =
                                       FStar_Syntax_Syntax.as_arg dec in
                                     let uu____1308 =
                                       let uu____1311 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec in
                                       [uu____1311] in
                                     uu____1307 :: uu____1308 in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____1306 in
                                 uu____1305 FStar_Pervasives_Native.None r in
                               let uu____1314 = FStar_Util.prefix formals2 in
                               (match uu____1314 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___93_1361 = last1 in
                                      let uu____1362 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1 in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___93_1361.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___93_1361.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____1362
                                      } in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)] in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1 in
                                    ((let uu____1392 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low in
                                      if uu____1392
                                      then
                                        let uu____1393 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l in
                                        let uu____1394 =
                                          FStar_Syntax_Print.term_to_string t in
                                        let uu____1395 =
                                          FStar_Syntax_Print.term_to_string
                                            t' in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____1393 uu____1394 uu____1395
                                      else ());
                                     (l, t'))))
                      | uu____1401 ->
                          raise
                            (FStar_Errors.Error
                               ("Annotated type of 'let rec' must be an arrow",
                                 (t.FStar_Syntax_Syntax.pos)))) in
               FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))
let rec tc_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      tc_maybe_toplevel_term
        (let uu___94_1834 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___94_1834.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___94_1834.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___94_1834.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___94_1834.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___94_1834.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___94_1834.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___94_1834.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___94_1834.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___94_1834.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___94_1834.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___94_1834.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___94_1834.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___94_1834.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___94_1834.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___94_1834.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___94_1834.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___94_1834.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___94_1834.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___94_1834.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___94_1834.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___94_1834.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___94_1834.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___94_1834.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___94_1834.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___94_1834.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___94_1834.FStar_TypeChecker_Env.is_native_tactic)
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
      (let uu____1846 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1846
       then
         let uu____1847 =
           let uu____1848 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1848 in
         let uu____1849 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1847 uu____1849
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1858 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1893 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1902 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1923 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1924 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1925 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1926 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1927 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1946 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1961 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1970 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1980 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1980 with
            | (e2,c,g) ->
                let g1 =
                  let uu___95_1997 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___95_1997.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___95_1997.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___95_1997.FStar_TypeChecker_Env.implicits)
                  } in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____2020 = FStar_Syntax_Util.type_u () in
           (match uu____2020 with
            | (t,u) ->
                let uu____2033 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____2033 with
                 | (e2,c,g) ->
                     let uu____2049 =
                       let uu____2066 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____2066 with
                       | (env2,uu____2090) -> tc_pats env2 pats in
                     (match uu____2049 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___96_2128 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___96_2128.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___96_2128.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___96_2128.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____2129 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              (FStar_Pervasives_Native.Some
                                 (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____2134 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____2129, c, uu____2134))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____2148 =
             let uu____2149 = FStar_Syntax_Subst.compress e1 in
             uu____2149.FStar_Syntax_Syntax.n in
           (match uu____2148 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____2160,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____2162;
                               FStar_Syntax_Syntax.lbtyp = uu____2163;
                               FStar_Syntax_Syntax.lbeff = uu____2164;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____2197 =
                  let uu____2204 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_TypeChecker_Common.t_unit in
                  tc_term uu____2204 e11 in
                (match uu____2197 with
                 | (e12,c1,g1) ->
                     let uu____2214 = tc_term env1 e2 in
                     (match uu____2214 with
                      | (e21,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.bind
                              e12.FStar_Syntax_Syntax.pos env1
                              (FStar_Pervasives_Native.Some e12) c1
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
                            let uu____2240 =
                              let uu____2245 =
                                let uu____2246 =
                                  let uu____2261 =
                                    let uu____2268 =
                                      let uu____2271 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_TypeChecker_Common.t_unit,
                                            e13) in
                                      [uu____2271] in
                                    (false, uu____2268) in
                                  (uu____2261, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____2246 in
                              FStar_Syntax_Syntax.mk uu____2245 in
                            uu____2240
                              (FStar_Pervasives_Native.Some
                                 ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
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
                              (FStar_Pervasives_Native.Some
                                 ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____2300 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____2300)))
            | uu____2305 ->
                let uu____2306 = tc_term env1 e1 in
                (match uu____2306 with
                 | (e2,c,g) ->
                     let e3 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (e2,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Sequence)))
                         (FStar_Pervasives_Native.Some
                            ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                         top.FStar_Syntax_Syntax.pos in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2332) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____2359 = tc_term env1 e1 in
           (match uu____2359 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    (FStar_Pervasives_Native.Some
                       ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____2387) ->
           let uu____2458 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2458 with
            | (env0,uu____2472) ->
                let uu____2477 = tc_comp env0 expected_c in
                (match uu____2477 with
                 | (expected_c1,uu____2491,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____2498 =
                       let uu____2505 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____2505 e1 in
                     (match uu____2498 with
                      | (e2,c',g') ->
                          let uu____2515 =
                            let uu____2522 =
                              let uu____2527 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____2527) in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____2522 in
                          (match uu____2515 with
                           | (e3,expected_c2,g'') ->
                               let e4 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_ascribed
                                      (e3,
                                        ((FStar_Util.Inl t_res),
                                          FStar_Pervasives_Native.None),
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Util.comp_effect_name
                                              expected_c2))))
                                   (FStar_Pervasives_Native.Some
                                      (t_res.FStar_Syntax_Syntax.n))
                                   top.FStar_Syntax_Syntax.pos in
                               let lc =
                                 FStar_Syntax_Util.lcomp_of_comp expected_c2 in
                               let f =
                                 let uu____2606 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____2606 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____2615 =
                                            FStar_Syntax_Util.mk_squash f1 in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____2615) in
                               let uu____2616 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____2616 with
                                | (e5,c,f2) ->
                                    let uu____2632 =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, uu____2632))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____2636) ->
           let uu____2707 = FStar_Syntax_Util.type_u () in
           (match uu____2707 with
            | (k,u) ->
                let uu____2720 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____2720 with
                 | (t1,uu____2734,f) ->
                     let uu____2736 =
                       let uu____2743 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____2743 e1 in
                     (match uu____2736 with
                      | (e2,c,g) ->
                          let uu____2753 =
                            let uu____2758 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____2762  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____2758 e2 c f in
                          (match uu____2753 with
                           | (c1,f1) ->
                               let uu____2771 =
                                 let uu____2778 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2,
                                          ((FStar_Util.Inl t1),
                                            FStar_Pervasives_Native.None),
                                          (FStar_Pervasives_Native.Some
                                             (c1.FStar_Syntax_Syntax.eff_name))))
                                     (FStar_Pervasives_Native.Some
                                        (t1.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____2778 c1 in
                               (match uu____2771 with
                                | (e3,c2,f2) ->
                                    let uu____2830 =
                                      let uu____2831 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____2831 in
                                    (e3, c2, uu____2830))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____2832;
              FStar_Syntax_Syntax.pos = uu____2833;
              FStar_Syntax_Syntax.vars = uu____2834;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2917 = FStar_Syntax_Util.head_and_args top in
           (match uu____2917 with
            | (unary_op,uu____2943) ->
                let head1 =
                  let uu____2977 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2977 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____3031);
              FStar_Syntax_Syntax.tk = uu____3032;
              FStar_Syntax_Syntax.pos = uu____3033;
              FStar_Syntax_Syntax.vars = uu____3034;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____3117 = FStar_Syntax_Util.head_and_args top in
           (match uu____3117 with
            | (unary_op,uu____3143) ->
                let head1 =
                  let uu____3177 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3177 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____3231;
              FStar_Syntax_Syntax.pos = uu____3232;
              FStar_Syntax_Syntax.vars = uu____3233;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____3280 =
               let uu____3287 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____3287 with | (env0,uu____3301) -> tc_term env0 e1 in
             match uu____3280 with
             | (e2,c,g) ->
                 let uu____3315 = FStar_Syntax_Util.head_and_args top in
                 (match uu____3315 with
                  | (reify_op,uu____3341) ->
                      let u_c =
                        let uu____3371 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____3371 with
                        | (uu____3378,c',uu____3380) ->
                            let uu____3381 =
                              let uu____3382 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____3382.FStar_Syntax_Syntax.n in
                            (match uu____3381 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____3388 ->
                                 let uu____3389 = FStar_Syntax_Util.type_u () in
                                 (match uu____3389 with
                                  | (t,u) ->
                                      let g_opt =
                                        FStar_TypeChecker_Rel.try_teq true
                                          env1 c'.FStar_Syntax_Syntax.res_typ
                                          t in
                                      ((match g_opt with
                                        | FStar_Pervasives_Native.Some g' ->
                                            FStar_TypeChecker_Rel.force_trivial_guard
                                              env1 g'
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____3401 =
                                              let uu____3402 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____3403 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____3404 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____3402 uu____3403
                                                uu____3404 in
                                            failwith uu____3401);
                                       u))) in
                      let repr =
                        let uu____3406 = c.FStar_Syntax_Syntax.comp () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____3406 u_c in
                      let e3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (reify_op, [(e2, aqual)]))
                          (FStar_Pervasives_Native.Some
                             (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____3431 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____3431
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____3432 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____3432 with
                       | (e4,c2,g') ->
                           let uu____3448 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____3448)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____3450;
              FStar_Syntax_Syntax.pos = uu____3451;
              FStar_Syntax_Syntax.vars = uu____3452;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____3508 =
               let uu____3509 =
                 let uu____3510 =
                   let uu____3515 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____3515, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____3510 in
               raise uu____3509 in
             let uu____3522 = FStar_Syntax_Util.head_and_args top in
             match uu____3522 with
             | (reflect_op,uu____3548) ->
                 let uu____3577 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____3577 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____3610 =
                        let uu____3611 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____3611 in
                      if uu____3610
                      then no_reflect ()
                      else
                        (let uu____3621 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____3621 with
                         | (env_no_ex,topt) ->
                             let uu____3640 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____3666 =
                                   let uu____3671 =
                                     let uu____3672 =
                                       let uu____3691 =
                                         let uu____3694 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____3695 =
                                           let uu____3698 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____3698] in
                                         uu____3694 :: uu____3695 in
                                       (repr, uu____3691) in
                                     FStar_Syntax_Syntax.Tm_app uu____3672 in
                                   FStar_Syntax_Syntax.mk uu____3671 in
                                 uu____3666 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos in
                               let uu____3705 =
                                 let uu____3712 =
                                   let uu____3713 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____3713
                                     FStar_Pervasives_Native.fst in
                                 tc_tot_or_gtot_term uu____3712 t in
                               match uu____3705 with
                               | (t1,uu____3745,g) ->
                                   let uu____3747 =
                                     let uu____3748 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____3748.FStar_Syntax_Syntax.n in
                                   (match uu____3747 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____3769,(res,uu____3771)::
                                         (wp,uu____3773)::[])
                                        -> (t1, res, wp, g)
                                    | uu____3840 -> failwith "Impossible") in
                             (match uu____3640 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____3883 =
                                    let uu____3888 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____3888 with
                                    | (e2,c,g) ->
                                        ((let uu____3903 =
                                            let uu____3904 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____3904 in
                                          if uu____3903
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____3914 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____3914 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____3922 =
                                                  let uu____3929 =
                                                    let uu____3934 =
                                                      let uu____3935 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____3936 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____3935 uu____3936 in
                                                    (uu____3934,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____3929] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____3922);
                                               (let uu____3945 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____3945)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____3947 =
                                                let uu____3948 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____3948 in
                                              (e2, uu____3947))) in
                                  (match uu____3883 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____3958 =
                                           let uu____3959 =
                                             let uu____3960 =
                                               let uu____3961 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____3961] in
                                             let uu____3962 =
                                               let uu____3973 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____3973] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____3960;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____3962;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____3959 in
                                         FStar_All.pipe_right uu____3958
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           (FStar_Pervasives_Native.Some
                                              (res_typ.FStar_Syntax_Syntax.n))
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____3997 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____3997 with
                                        | (e4,c1,g') ->
                                            let uu____4013 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____4013))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____4076 =
               let uu____4077 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____4077 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____4076 instantiate_both in
           ((let uu____4093 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____4093
             then
               let uu____4094 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____4095 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____4094
                 uu____4095
             else ());
            (let isquote =
               match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.quote_lid
                   -> true
               | uu____4099 -> false in
             let uu____4100 = tc_term (no_inst env2) head1 in
             match uu____4100 with
             | (head2,chead,g_head) ->
                 let uu____4116 =
                   let uu____4123 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____4123
                   then
                     let uu____4130 =
                       let uu____4137 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____4137 in
                     match uu____4130 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____4150 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____4152 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c in
                                 Prims.op_Negation uu____4152))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                           if uu____4150
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c in
                         (e1, c1, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2 in
                      let uu____4157 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env3 head2 chead g_head args
                        uu____4157) in
                 (match uu____4116 with
                  | (e1,c,g) ->
                      ((let uu____4170 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____4170
                        then
                          let uu____4171 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____4171
                        else ());
                       (let uu____4173 = comp_check_expected_typ env0 e1 c in
                        match uu____4173 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____4190 =
                                let uu____4191 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____4191.FStar_Syntax_Syntax.n in
                              match uu____4190 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____4197) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___97_4275 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___97_4275.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___97_4275.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___97_4275.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____4332 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____4334 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____4334 in
                            ((let uu____4336 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____4336
                              then
                                let uu____4337 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____4338 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____4337 uu____4338
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____4390 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____4390 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____4410 = tc_term env12 e1 in
                (match uu____4410 with
                 | (e11,c1,g1) ->
                     let uu____4426 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____4436 = FStar_Syntax_Util.type_u () in
                           (match uu____4436 with
                            | (k,uu____4446) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____4448 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____4448, res_t)) in
                     (match uu____4426 with
                      | (env_branches,res_t) ->
                          ((let uu____4458 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____4458
                            then
                              let uu____4459 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____4459
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____4553 =
                              let uu____4558 =
                                FStar_List.fold_right
                                  (fun uu____4604  ->
                                     fun uu____4605  ->
                                       match (uu____4604, uu____4605) with
                                       | ((uu____4668,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____4728 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____4728))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____4558 with
                              | (cases,g) ->
                                  let uu____4767 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____4767, g) in
                            match uu____4553 with
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
                                           (fun uu____4871  ->
                                              match uu____4871 with
                                              | ((pat,wopt,br),uu____4899,lc,uu____4901)
                                                  ->
                                                  let uu____4914 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____4914))) in
                                    let e2 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_match
                                           (scrutinee, branches))
                                        (FStar_Pervasives_Native.Some
                                           ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
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
                                  let uu____4991 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____4991
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____5002 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____5002 in
                                     let lb =
                                       let uu____5008 =
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
                                           uu____5008;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____5014 =
                                         let uu____5019 =
                                           let uu____5020 =
                                             let uu____5035 =
                                               let uu____5036 =
                                                 let uu____5037 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____5037] in
                                               FStar_Syntax_Subst.close
                                                 uu____5036 e_match in
                                             ((false, [lb]), uu____5035) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____5020 in
                                         FStar_Syntax_Syntax.mk uu____5019 in
                                       uu____5014
                                         (FStar_Pervasives_Native.Some
                                            ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____5051 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____5051
                                  then
                                    let uu____5052 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____5053 =
                                      let uu____5054 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____5054 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____5052 uu____5053
                                  else ());
                                 (let uu____5056 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____5056))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5061;
                FStar_Syntax_Syntax.lbunivs = uu____5062;
                FStar_Syntax_Syntax.lbtyp = uu____5063;
                FStar_Syntax_Syntax.lbeff = uu____5064;
                FStar_Syntax_Syntax.lbdef = uu____5065;_}::[]),uu____5066)
           ->
           ((let uu____5094 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5094
             then
               let uu____5095 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____5095
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____5097),uu____5098) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5117;
                FStar_Syntax_Syntax.lbunivs = uu____5118;
                FStar_Syntax_Syntax.lbtyp = uu____5119;
                FStar_Syntax_Syntax.lbeff = uu____5120;
                FStar_Syntax_Syntax.lbdef = uu____5121;_}::uu____5122),uu____5123)
           ->
           ((let uu____5153 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5153
             then
               let uu____5154 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____5154
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____5156),uu____5157) ->
           check_inner_let_rec env1 top)
and tc_synth:
  FStar_TypeChecker_Env.env ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
       FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun args  ->
      fun rng  ->
        let uu____5189 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5307))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5389))::(uu____5390,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____5391))::
              (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____5492 ->
              raise
                (FStar_Errors.Error ("synth_by_tactic: bad application", rng)) in
        match uu____5189 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____5606 = FStar_TypeChecker_Env.expected_typ env in
                  (match uu____5606 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____5614 =
                         let uu____5615 =
                           let uu____5620 =
                             FStar_TypeChecker_Env.get_range env in
                           ("synth_by_tactic: need a type annotation when no expected type is present",
                             uu____5620) in
                         FStar_Errors.Error uu____5615 in
                       raise uu____5614) in
            let uu____5625 = FStar_TypeChecker_Env.clear_expected_typ env in
            (match uu____5625 with
             | (env',uu____5639) ->
                 let uu____5644 = tc_term env' typ in
                 (match uu____5644 with
                  | (typ1,uu____5658,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____5661 = tc_term env' tau in
                        match uu____5661 with
                        | (tau1,c,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let uu____5679 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Tac") in
                              if uu____5679
                              then
                                let uu____5680 =
                                  FStar_Syntax_Print.term_to_string tau1 in
                                let uu____5681 =
                                  FStar_Syntax_Print.term_to_string typ1 in
                                FStar_Util.print2
                                  "Running tactic %s at return type %s\n"
                                  uu____5680 uu____5681
                              else ());
                             (let t =
                                env.FStar_TypeChecker_Env.synth env' typ1
                                  tau1 in
                              (let uu____5685 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "Tac") in
                               if uu____5685
                               then
                                 let uu____5686 =
                                   FStar_Syntax_Print.term_to_string t in
                                 FStar_Util.print1 "Got %s\n" uu____5686
                               else ());
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____5689 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng in
                               tc_term env uu____5689)))))))
and tc_tactic_opt:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun topt  ->
      match topt with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some tactic ->
          let uu____5713 =
            tc_check_tot_or_gtot_term env tactic
              FStar_TypeChecker_Common.t_tactic_unit in
          (match uu____5713 with
           | (tactic1,uu____5723,uu____5724) ->
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
        let uu____5763 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____5763 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____5784 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____5784
              then FStar_Util.Inl t1
              else
                (let uu____5790 =
                   let uu____5791 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____5791 in
                 FStar_Util.Inr uu____5790) in
            let is_data_ctor uu___86_5805 =
              match uu___86_5805 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____5808) -> true
              | uu____5815 -> false in
            let uu____5818 =
              (is_data_ctor dc) &&
                (let uu____5820 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____5820) in
            if uu____5818
            then
              let uu____5827 =
                let uu____5828 =
                  let uu____5833 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____5834 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____5833, uu____5834) in
                FStar_Errors.Error uu____5828 in
              raise uu____5827
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____5851 =
            let uu____5852 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____5852 in
          failwith uu____5851
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____5894 =
              let uu____5895 = FStar_Syntax_Subst.compress t1 in
              uu____5895.FStar_Syntax_Syntax.n in
            match uu____5894 with
            | FStar_Syntax_Syntax.Tm_arrow uu____5900 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____5915 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___98_5961 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___98_5961.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___98_5961.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___98_5961.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____6023 =
            let uu____6036 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____6036 with
            | FStar_Pervasives_Native.None  ->
                let uu____6051 = FStar_Syntax_Util.type_u () in
                (match uu____6051 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____6023 with
           | (t,uu____6088,g0) ->
               let uu____6102 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____6102 with
                | (e1,uu____6122,g1) ->
                    let uu____6136 =
                      let uu____6137 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____6137
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____6138 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____6136, uu____6138)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____6140 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____6157 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____6157)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____6140 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___99_6182 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___99_6182.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___99_6182.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Common.insert_bv x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____6185 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____6185 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____6206 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____6206
                       then FStar_Util.Inl t1
                       else
                         (let uu____6212 =
                            let uu____6213 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____6213 in
                          FStar_Util.Inr uu____6212) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____6223;
             FStar_Syntax_Syntax.pos = uu____6224;
             FStar_Syntax_Syntax.vars = uu____6225;_},uu____6226)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____6235 =
            let uu____6236 =
              let uu____6241 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____6241) in
            FStar_Errors.Error uu____6236 in
          raise uu____6235
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____6249 =
            let uu____6250 =
              let uu____6255 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____6255) in
            FStar_Errors.Error uu____6250 in
          raise uu____6249
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____6263;
             FStar_Syntax_Syntax.pos = uu____6264;
             FStar_Syntax_Syntax.vars = uu____6265;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____6278 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6278 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____6301 =
                     let uu____6302 =
                       let uu____6307 =
                         let uu____6308 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____6309 =
                           FStar_Util.string_of_int (FStar_List.length us1) in
                         let uu____6310 =
                           FStar_Util.string_of_int (FStar_List.length us') in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____6308 uu____6309 uu____6310 in
                       let uu____6311 = FStar_TypeChecker_Env.get_range env1 in
                       (uu____6307, uu____6311) in
                     FStar_Errors.Error uu____6302 in
                   raise uu____6301)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____6327 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Common.insert_fv fv' t;
                 (let e1 =
                    let uu____6331 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        (FStar_Pervasives_Native.Some
                           (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6331 us1 in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6333 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6333 with
           | ((us,t),range) ->
               ((let uu____6356 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____6356
                 then
                   let uu____6357 =
                     let uu____6358 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____6358 in
                   let uu____6359 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____6360 = FStar_Range.string_of_range range in
                   let uu____6361 = FStar_Range.string_of_use_range range in
                   let uu____6362 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____6357 uu____6359 uu____6360 uu____6361 uu____6362
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Common.insert_fv fv' t;
                 (let e1 =
                    let uu____6367 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        (FStar_Pervasives_Native.Some
                           (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6367 us in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant top.FStar_Syntax_Syntax.pos c in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.n))
              e.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6397 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6397 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____6411 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____6411 with
                | (env2,uu____6425) ->
                    let uu____6430 = tc_binders env2 bs1 in
                    (match uu____6430 with
                     | (bs2,env3,g,us) ->
                         let uu____6449 = tc_comp env3 c1 in
                         (match uu____6449 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___100_6470 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___100_6470.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___100_6470.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___100_6470.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____6483 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____6483 in
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
              (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.n))
              top.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____6514 =
            let uu____6519 =
              let uu____6520 = FStar_Syntax_Syntax.mk_binder x in
              [uu____6520] in
            FStar_Syntax_Subst.open_term uu____6519 phi in
          (match uu____6514 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____6530 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____6530 with
                | (env2,uu____6544) ->
                    let uu____6549 =
                      let uu____6562 = FStar_List.hd x1 in
                      tc_binder env2 uu____6562 in
                    (match uu____6549 with
                     | (x2,env3,f1,u) ->
                         ((let uu____6590 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____6590
                           then
                             let uu____6591 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____6592 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____6593 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____6591 uu____6592 uu____6593
                           else ());
                          (let uu____6595 = FStar_Syntax_Util.type_u () in
                           match uu____6595 with
                           | (t_phi,uu____6607) ->
                               let uu____6608 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____6608 with
                                | (phi2,uu____6622,f2) ->
                                    let e1 =
                                      let uu___101_6629 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___101_6629.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___101_6629.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___101_6629.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____6640 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____6640 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____6655) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____6682 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____6682
            then
              let uu____6683 =
                FStar_Syntax_Print.term_to_string
                  (let uu___102_6686 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.tk =
                       (uu___102_6686.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___102_6686.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___102_6686.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____6683
            else ());
           (let uu____6694 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____6694 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____6707 ->
          let uu____6708 =
            let uu____6709 = FStar_Syntax_Print.term_to_string top in
            let uu____6710 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____6709
              uu____6710 in
          failwith uu____6708
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____6719 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____6720,FStar_Pervasives_Native.None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int
          (uu____6731,FStar_Pervasives_Native.Some uu____6732) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____6747 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____6754 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____6755 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____6756 ->
          FStar_TypeChecker_Common.t_range
      | uu____6757 -> raise (FStar_Errors.Error ("Unsupported constant", r))
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
      | FStar_Syntax_Syntax.Total (t,uu____6774) ->
          let uu____6787 = FStar_Syntax_Util.type_u () in
          (match uu____6787 with
           | (k,u) ->
               let uu____6800 = tc_check_tot_or_gtot_term env t k in
               (match uu____6800 with
                | (t1,uu____6814,g) ->
                    let uu____6816 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____6816, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____6818) ->
          let uu____6831 = FStar_Syntax_Util.type_u () in
          (match uu____6831 with
           | (k,u) ->
               let uu____6844 = tc_check_tot_or_gtot_term env t k in
               (match uu____6844 with
                | (t1,uu____6858,g) ->
                    let uu____6860 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____6860, u, g)))
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
            let uu____6870 =
              let uu____6871 =
                let uu____6872 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____6872 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____6871 in
            uu____6870 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____6875 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____6875 with
           | (tc1,uu____6889,f) ->
               let uu____6891 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____6891 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____6947 =
                        let uu____6948 = FStar_Syntax_Subst.compress head3 in
                        uu____6948.FStar_Syntax_Syntax.n in
                      match uu____6947 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____6953,us) -> us
                      | uu____6963 -> [] in
                    let uu____6964 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____6964 with
                     | (uu____6989,args1) ->
                         let uu____7019 =
                           let uu____7042 = FStar_List.hd args1 in
                           let uu____7059 = FStar_List.tl args1 in
                           (uu____7042, uu____7059) in
                         (match uu____7019 with
                          | (res,args2) ->
                              let uu____7140 =
                                let uu____7149 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___87_7177  ->
                                          match uu___87_7177 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____7187 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____7187 with
                                               | (env1,uu____7199) ->
                                                   let uu____7204 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____7204 with
                                                    | (e1,uu____7216,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____7149
                                  FStar_List.unzip in
                              (match uu____7140 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___103_7257 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___103_7257.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___103_7257.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____7263 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____7263 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____7267 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____7267))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____7275 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____7276 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____7286 = aux u3 in FStar_Syntax_Syntax.U_succ uu____7286
        | FStar_Syntax_Syntax.U_max us ->
            let uu____7290 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____7290
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____7295 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____7295 FStar_Pervasives_Native.snd
         | uu____7304 -> aux u)
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
            let uu____7328 =
              let uu____7329 =
                let uu____7334 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____7334, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____7329 in
            raise uu____7328 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____7424 bs2 bs_expected1 =
              match uu____7424 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____7592)) ->
                             let uu____7597 =
                               let uu____7598 =
                                 let uu____7603 =
                                   let uu____7604 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____7604 in
                                 let uu____7605 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____7603, uu____7605) in
                               FStar_Errors.Error uu____7598 in
                             raise uu____7597
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____7606),FStar_Pervasives_Native.None ) ->
                             let uu____7611 =
                               let uu____7612 =
                                 let uu____7617 =
                                   let uu____7618 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____7618 in
                                 let uu____7619 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____7617, uu____7619) in
                               FStar_Errors.Error uu____7612 in
                             raise uu____7611
                         | uu____7620 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____7626 =
                           let uu____7631 =
                             let uu____7632 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____7632.FStar_Syntax_Syntax.n in
                           match uu____7631 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____7641 ->
                               ((let uu____7643 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____7643
                                 then
                                   let uu____7644 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____7644
                                 else ());
                                (let uu____7646 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____7646 with
                                 | (t,uu____7658,g1) ->
                                     let g2 =
                                       let uu____7661 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____7662 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____7661
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____7662 in
                                     let g3 =
                                       let uu____7664 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____7664 in
                                     (t, g3))) in
                         match uu____7626 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___104_7692 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___104_7692.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___104_7692.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____7705 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____7705 in
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
                  | uu____7869 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____7876 = tc_binders env1 bs in
                  match uu____7876 with
                  | (bs1,envbody,g,uu____7914) ->
                      let uu____7915 =
                        let uu____7928 =
                          let uu____7929 = FStar_Syntax_Subst.compress body1 in
                          uu____7929.FStar_Syntax_Syntax.n in
                        match uu____7928 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____7949) ->
                            let uu____8020 = tc_comp envbody c in
                            (match uu____8020 with
                             | (c1,uu____8040,g') ->
                                 let uu____8042 =
                                   tc_tactic_opt envbody tacopt in
                                 let uu____8045 =
                                   FStar_TypeChecker_Rel.conj_guard g g' in
                                 ((FStar_Pervasives_Native.Some c1),
                                   uu____8042, body1, uu____8045))
                        | uu____8050 ->
                            (FStar_Pervasives_Native.None,
                              FStar_Pervasives_Native.None, body1, g) in
                      (match uu____7915 with
                       | (copt,tacopt,body2,g1) ->
                           (FStar_Pervasives_Native.None, bs1, [], copt,
                             tacopt, envbody, body2, g1))))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____8154 =
                    let uu____8155 = FStar_Syntax_Subst.compress t2 in
                    uu____8155.FStar_Syntax_Syntax.n in
                  match uu____8154 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____8188 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8214 -> failwith "Impossible");
                       (let uu____8221 = tc_binders env1 bs in
                        match uu____8221 with
                        | (bs1,envbody,g,uu____8261) ->
                            let uu____8262 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____8262 with
                             | (envbody1,uu____8298) ->
                                 ((FStar_Pervasives_Native.Some (t2, true)),
                                   bs1, [], FStar_Pervasives_Native.None,
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____8319;
                         FStar_Syntax_Syntax.tk = uu____8320;
                         FStar_Syntax_Syntax.pos = uu____8321;
                         FStar_Syntax_Syntax.vars = uu____8322;_},uu____8323)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8377 -> failwith "Impossible");
                       (let uu____8384 = tc_binders env1 bs in
                        match uu____8384 with
                        | (bs1,envbody,g,uu____8424) ->
                            let uu____8425 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____8425 with
                             | (envbody1,uu____8461) ->
                                 ((FStar_Pervasives_Native.Some (t2, true)),
                                   bs1, [], FStar_Pervasives_Native.None,
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____8483) ->
                      let uu____8492 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____8492 with
                       | (uu____8549,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some (t2, false)), bs1,
                             bs', copt, tacopt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____8619 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____8619 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____8727 c_expected2 =
                               match uu____8727 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____8842 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____8842)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____8873 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____8873 in
                                        let uu____8874 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____8874)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        if FStar_Syntax_Util.is_named_tot c
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
                                               let uu____8950 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____8950 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____8971 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____8971 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____9019 =
                                                           let uu____9050 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____9050,
                                                             subst2) in
                                                         handle_more
                                                           uu____9019
                                                           c_expected4))
                                           | uu____9067 ->
                                               let uu____9068 =
                                                 let uu____9069 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____9069 in
                                               fail uu____9068 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____9099 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____9099 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___105_9162 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___105_9162.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___105_9162.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___105_9162.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___105_9162.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___105_9162.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___105_9162.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___105_9162.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___105_9162.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___105_9162.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___105_9162.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___105_9162.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___105_9162.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___105_9162.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___105_9162.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___105_9162.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___105_9162.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___105_9162.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___105_9162.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___105_9162.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___105_9162.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___105_9162.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___105_9162.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___105_9162.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___105_9162.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___105_9162.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___105_9162.FStar_TypeChecker_Env.is_native_tactic)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____9201  ->
                                     fun uu____9202  ->
                                       match (uu____9201, uu____9202) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____9247 =
                                             let uu____9254 =
                                               let uu____9255 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____9255
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____9254 t3 in
                                           (match uu____9247 with
                                            | (t4,uu____9277,uu____9278) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____9288 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___106_9291
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___106_9291.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___106_9291.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____9288 ::
                                                        letrec_binders
                                                  | uu____9292 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____9297 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____9297 with
                            | (envbody,bs1,g,c) ->
                                let uu____9356 =
                                  let uu____9363 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____9363
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____9356 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((FStar_Pervasives_Native.Some
                                         (t2, false)), bs1, letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       FStar_Pervasives_Native.None,
                                       envbody2, body1, g))))
                  | uu____9430 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____9459 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____9459
                      else
                        (let uu____9461 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1 in
                         match uu____9461 with
                         | (uu____9516,bs1,uu____9518,c_opt,tacopt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some (t2, false)),
                               bs1, [], c_opt, tacopt, envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____9561 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____9561 with
          | (env1,topt) ->
              ((let uu____9581 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____9581
                then
                  let uu____9582 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____9582
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____9586 = expected_function_typ1 env1 topt body in
                match uu____9586 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____9647 =
                      tc_term
                        (let uu___107_9656 = envbody in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___107_9656.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___107_9656.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___107_9656.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___107_9656.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___107_9656.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___107_9656.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___107_9656.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___107_9656.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___107_9656.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___107_9656.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___107_9656.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___107_9656.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___107_9656.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___107_9656.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___107_9656.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___107_9656.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___107_9656.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___107_9656.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___107_9656.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___107_9656.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___107_9656.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___107_9656.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___107_9656.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___107_9656.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___107_9656.FStar_TypeChecker_Env.is_native_tactic)
                         }) body1 in
                    (match uu____9647 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body in
                         ((let uu____9668 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits") in
                           if uu____9668
                           then
                             let uu____9669 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits) in
                             let uu____9682 =
                               let uu____9683 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____9683 in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____9669 uu____9682
                           else ());
                          (let uu____9685 =
                             let uu____9692 =
                               let uu____9697 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               (body2, uu____9697) in
                             check_expected_effect
                               (let uu___108_9708 = envbody in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___108_9708.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___108_9708.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___108_9708.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___108_9708.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___108_9708.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___108_9708.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___108_9708.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___108_9708.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___108_9708.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___108_9708.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___108_9708.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___108_9708.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___108_9708.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___108_9708.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___108_9708.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___108_9708.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___108_9708.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___108_9708.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___108_9708.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___108_9708.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___108_9708.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___108_9708.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___108_9708.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___108_9708.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___108_9708.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___108_9708.FStar_TypeChecker_Env.is_native_tactic)
                                }) c_opt uu____9692 in
                           match uu____9685 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard in
                               let guard2 =
                                 let uu____9720 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____9722 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1 in
                                      Prims.op_Negation uu____9722) in
                                 if uu____9720
                                 then
                                   let uu____9723 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1 in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____9723
                                 else
                                   (let guard2 =
                                      let uu____9726 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1 in
                                      FStar_TypeChecker_Rel.close_guard env1
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____9726 in
                                    guard2) in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1 in
                               let e =
                                 FStar_Syntax_Util.abs bs1 body3
                                   (FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         (FStar_Util.dflt cbody1 c_opt))) in
                               let uu____9737 =
                                 match tfun_opt with
                                 | FStar_Pervasives_Native.Some (t,use_teq)
                                     ->
                                     let t1 = FStar_Syntax_Subst.compress t in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____9763 -> (e, t1, guard2)
                                      | uu____9778 ->
                                          let uu____9779 =
                                            if use_teq
                                            then
                                              let uu____9788 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed in
                                              (e, uu____9788)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1 in
                                          (match uu____9779 with
                                           | (e1,guard') ->
                                               let uu____9798 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard' in
                                               (e1, t1, uu____9798)))
                                 | FStar_Pervasives_Native.None  ->
                                     (e, tfun_computed, guard2) in
                               (match uu____9737 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1 in
                                    let uu____9818 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        FStar_Pervasives_Native.None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3 in
                                    (match uu____9818 with
                                     | (c1,g1) -> (e1, c1, g1))))))))
and check_application_args:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
             FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                 FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.lcomp,
                FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3
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
              (let uu____9873 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____9873
               then
                 let uu____9874 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____9875 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____9874
                   uu____9875
               else ());
              (let monadic_application uu____9934 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____9934 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___109_9995 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___109_9995.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___109_9995.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___109_9995.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____9996 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
                       | uu____10011 ->
                           let g =
                             let uu____10019 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____10019
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____10020 =
                             let uu____10021 =
                               let uu____10026 =
                                 let uu____10027 =
                                   let uu____10028 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____10028 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____10027 in
                               FStar_Syntax_Syntax.mk_Total uu____10026 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____10021 in
                           (uu____10020, g) in
                     (match uu____9996 with
                      | (cres2,guard1) ->
                          ((let uu____10046 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____10046
                            then
                              let uu____10047 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____10047
                            else ());
                           (let cres3 =
                              let uu____10050 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____10050
                              then
                                let term =
                                  FStar_Syntax_Syntax.mk_Tm_app head2
                                    (FStar_List.rev arg_rets_rev)
                                    FStar_Pervasives_Native.None
                                    head2.FStar_Syntax_Syntax.pos in
                                FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                  env term cres2
                              else cres2 in
                            let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____10090  ->
                                     match uu____10090 with
                                     | ((e,q),x,c) ->
                                         let uu____10131 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____10131
                                         then
                                           FStar_TypeChecker_Util.bind
                                             e.FStar_Syntax_Syntax.pos env
                                             (FStar_Pervasives_Native.Some e)
                                             c (x, out_c)
                                         else
                                           FStar_TypeChecker_Util.bind
                                             e.FStar_Syntax_Syntax.pos env
                                             FStar_Pervasives_Native.None c
                                             (x, out_c)) cres3 arg_comps_rev in
                            let comp1 =
                              FStar_TypeChecker_Util.bind
                                head2.FStar_Syntax_Syntax.pos env
                                FStar_Pervasives_Native.None chead1
                                (FStar_Pervasives_Native.None, comp) in
                            let shortcuts_evaluation_order =
                              let uu____10145 =
                                let uu____10146 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____10146.FStar_Syntax_Syntax.n in
                              match uu____10145 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____10152 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____10173  ->
                                         match uu____10173 with
                                         | (arg,uu____10187,uu____10188) ->
                                             arg :: args1) [] arg_comps_rev in
                                let app =
                                  FStar_Syntax_Syntax.mk_Tm_app head2 args1
                                    (FStar_Pervasives_Native.Some
                                       ((comp1.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                    r in
                                let app1 =
                                  FStar_TypeChecker_Util.maybe_lift env app
                                    cres3.FStar_Syntax_Syntax.eff_name
                                    comp1.FStar_Syntax_Syntax.eff_name
                                    comp1.FStar_Syntax_Syntax.res_typ in
                                FStar_TypeChecker_Util.maybe_monadic env app1
                                  comp1.FStar_Syntax_Syntax.eff_name
                                  comp1.FStar_Syntax_Syntax.res_typ
                              else
                                (let uu____10200 =
                                   let map_fun uu____10266 =
                                     match uu____10266 with
                                     | ((e,q),uu____10303,c) ->
                                         let uu____10313 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____10313
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
                                                comp1.FStar_Syntax_Syntax.eff_name
                                                c.FStar_Syntax_Syntax.res_typ in
                                            let uu____10369 =
                                              let uu____10374 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____10374, q) in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____10369)) in
                                   let uu____10409 =
                                     let uu____10436 =
                                       let uu____10461 =
                                         let uu____10476 =
                                           let uu____10485 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____10485,
                                             FStar_Pervasives_Native.None,
                                             chead1) in
                                         uu____10476 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____10461 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____10436 in
                                   match uu____10409 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____10672 =
                                         let uu____10673 =
                                           FStar_List.hd reverse_args in
                                         FStar_Pervasives_Native.fst
                                           uu____10673 in
                                       let uu____10682 =
                                         let uu____10689 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____10689 in
                                       (lifted_args, uu____10672,
                                         uu____10682) in
                                 match uu____10200 with
                                 | (lifted_args,head3,args1) ->
                                     let app =
                                       FStar_Syntax_Syntax.mk_Tm_app head3
                                         args1
                                         (FStar_Pervasives_Native.Some
                                            ((comp1.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         r in
                                     let app1 =
                                       FStar_TypeChecker_Util.maybe_lift env
                                         app
                                         cres3.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.res_typ in
                                     let app2 =
                                       FStar_TypeChecker_Util.maybe_monadic
                                         env app1
                                         comp1.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.res_typ in
                                     let bind_lifted_args e uu___88_10804 =
                                       match uu___88_10804 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____10881 =
                                               let uu____10886 =
                                                 let uu____10887 =
                                                   let uu____10902 =
                                                     let uu____10903 =
                                                       let uu____10904 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____10904] in
                                                     FStar_Syntax_Subst.close
                                                       uu____10903 e in
                                                   ((false, [lb]),
                                                     uu____10902) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____10887 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10886 in
                                             uu____10881
                                               FStar_Pervasives_Native.None
                                               e.FStar_Syntax_Syntax.pos in
                                           FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_meta
                                                (letbinding,
                                                  (FStar_Syntax_Syntax.Meta_monadic
                                                     (m,
                                                       (comp1.FStar_Syntax_Syntax.res_typ)))))
                                             FStar_Pervasives_Native.None
                                             e.FStar_Syntax_Syntax.pos in
                                     FStar_List.fold_left bind_lifted_args
                                       app2 lifted_args) in
                            let uu____10943 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp1
                                guard1 in
                            match uu____10943 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____11036 bs args1 =
                 match uu____11036 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____11187))::rest,
                         (uu____11189,FStar_Pervasives_Native.None )::uu____11190)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t in
                          let uu____11261 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____11261 with
                           | (varg,uu____11281,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____11303 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____11303) in
                               let uu____11304 =
                                 let uu____11339 =
                                   let uu____11354 =
                                     let uu____11367 =
                                       let uu____11368 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____11368
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____11367) in
                                   uu____11354 :: outargs in
                                 let uu____11387 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____11339, (arg :: arg_rets),
                                   uu____11387, fvs) in
                               tc_args head_info uu____11304 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____11499),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11500)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____11513 ->
                                raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___110_11524 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___110_11524.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___110_11524.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____11526 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____11526
                             then
                               let uu____11527 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____11527
                             else ());
                            (let targ1 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___111_11532 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___111_11532.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___111_11532.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___111_11532.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___111_11532.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___111_11532.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___111_11532.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___111_11532.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___111_11532.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___111_11532.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___111_11532.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___111_11532.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___111_11532.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___111_11532.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___111_11532.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___111_11532.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___111_11532.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___111_11532.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___111_11532.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___111_11532.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___111_11532.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___111_11532.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___111_11532.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___111_11532.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___111_11532.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___111_11532.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___111_11532.FStar_TypeChecker_Env.is_native_tactic)
                               } in
                             (let uu____11534 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____11534
                              then
                                let uu____11535 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____11536 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11537 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____11535 uu____11536 uu____11537
                              else ());
                             (let uu____11539 = tc_term env2 e in
                              match uu____11539 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____11566 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____11566 in
                                  let uu____11567 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____11567
                                  then
                                    let subst2 =
                                      let uu____11575 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____11575
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
                      | (uu____11669,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____11709) ->
                          let uu____11768 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____11768 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____11802 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____11802
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____11831 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____11831 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____11854 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____11854
                                            then
                                              let uu____11855 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____11855
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____11897 when Prims.op_Negation norm1
                                     ->
                                     let uu____11898 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____11898
                                 | uu____11899 ->
                                     let uu____11900 =
                                       let uu____11901 =
                                         let uu____11906 =
                                           let uu____11907 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____11908 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____11907 uu____11908 in
                                         let uu____11915 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____11906, uu____11915) in
                                       FStar_Errors.Error uu____11901 in
                                     raise uu____11900 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____11936 =
                   let uu____11937 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____11937.FStar_Syntax_Syntax.n in
                 match uu____11936 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____11952 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____12061 = tc_term env1 e in
                           (match uu____12061 with
                            | (e1,c,g_e) ->
                                let uu____12083 = tc_args1 env1 tl1 in
                                (match uu____12083 with
                                 | (args2,comps,g_rest) ->
                                     let uu____12123 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____12123))) in
                     let uu____12144 = tc_args1 env args in
                     (match uu____12144 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____12183 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____12225  ->
                                      match uu____12225 with
                                      | (uu____12240,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____12183 in
                          let ml_or_tot t r1 =
                            let uu____12263 = FStar_Options.ml_ish () in
                            if uu____12263
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____12266 =
                              let uu____12271 =
                                let uu____12272 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____12272
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____12271 in
                            ml_or_tot uu____12266 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____12287 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____12287
                            then
                              let uu____12288 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____12289 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____12290 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____12288 uu____12289 uu____12290
                            else ());
                           (let uu____12293 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____12293);
                           (let comp =
                              let uu____12295 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____12308  ->
                                   fun out  ->
                                     match uu____12308 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____12295 in
                            let uu____12322 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                (FStar_Pervasives_Native.Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____12327 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____12322, comp, uu____12327))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____12332;
                        FStar_Syntax_Syntax.tk = uu____12333;
                        FStar_Syntax_Syntax.pos = uu____12334;
                        FStar_Syntax_Syntax.vars = uu____12335;_},uu____12336)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____12473 = tc_term env1 e in
                           (match uu____12473 with
                            | (e1,c,g_e) ->
                                let uu____12495 = tc_args1 env1 tl1 in
                                (match uu____12495 with
                                 | (args2,comps,g_rest) ->
                                     let uu____12535 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____12535))) in
                     let uu____12556 = tc_args1 env args in
                     (match uu____12556 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____12595 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____12637  ->
                                      match uu____12637 with
                                      | (uu____12652,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____12595 in
                          let ml_or_tot t r1 =
                            let uu____12675 = FStar_Options.ml_ish () in
                            if uu____12675
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____12678 =
                              let uu____12683 =
                                let uu____12684 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____12684
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____12683 in
                            ml_or_tot uu____12678 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____12699 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____12699
                            then
                              let uu____12700 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____12701 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____12702 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____12700 uu____12701 uu____12702
                            else ());
                           (let uu____12705 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____12705);
                           (let comp =
                              let uu____12707 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____12720  ->
                                   fun out  ->
                                     match uu____12720 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____12707 in
                            let uu____12734 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                (FStar_Pervasives_Native.Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____12739 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____12734, comp, uu____12739))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____12766 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____12766 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____12833) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____12843,uu____12844) -> check_function_app t
                 | uu____12901 ->
                     let uu____12902 =
                       let uu____12903 =
                         let uu____12908 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____12908, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____12903 in
                     raise uu____12902 in
               check_function_app thead)
and check_short_circuit_args:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
             FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
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
                  let uu____12990 =
                    FStar_List.fold_left2
                      (fun uu____13035  ->
                         fun uu____13036  ->
                           fun uu____13037  ->
                             match (uu____13035, uu____13036, uu____13037)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____13115 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____13115 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____13133 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____13133 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____13137 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____13137)
                                              &&
                                              (let uu____13139 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____13139)) in
                                       let uu____13140 =
                                         let uu____13151 =
                                           let uu____13162 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____13162] in
                                         FStar_List.append seen uu____13151 in
                                       let uu____13171 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____13140, uu____13171, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____12990 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           (FStar_Pervasives_Native.Some
                              (res_t.FStar_Syntax_Syntax.n)) r in
                       let c1 =
                         if ghost
                         then
                           let uu____13215 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____13215
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____13217 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____13217 with | (c2,g) -> (e, c2, g)))
              | uu____13236 ->
                  check_application_args env head1 chead g_head args
                    expected_topt
and tc_eqn:
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,(FStar_Syntax_Syntax.term',
                                                                 FStar_Syntax_Syntax.term')
                                                                 FStar_Syntax_Syntax.syntax
                                                                 FStar_Pervasives_Native.option,
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 ->
        ((FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                                    FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple3,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,
          FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple4
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____13274 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____13274 with
        | (pattern,when_clause,branch_exp) ->
            let uu____13318 = branch1 in
            (match uu____13318 with
             | (cpat,uu____13354,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____13414 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 in
                   match uu____13414 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____13443 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____13443
                         then
                           let uu____13444 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____13445 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____13444 uu____13445
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____13448 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____13448 with
                         | (env1,uu____13468) ->
                             let env11 =
                               let uu___112_13474 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___112_13474.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___112_13474.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___112_13474.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___112_13474.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___112_13474.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___112_13474.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___112_13474.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___112_13474.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___112_13474.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___112_13474.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___112_13474.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___112_13474.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___112_13474.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___112_13474.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___112_13474.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___112_13474.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___112_13474.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___112_13474.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___112_13474.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___112_13474.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___112_13474.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___112_13474.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___112_13474.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___112_13474.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___112_13474.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___112_13474.FStar_TypeChecker_Env.is_native_tactic)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____13477 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____13477
                               then
                                 let uu____13478 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____13479 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____13478 uu____13479
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t in
                               let uu____13482 =
                                 tc_tot_or_gtot_term env12 exp in
                               match uu____13482 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___113_13505 = g in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___113_13505.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___113_13505.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___113_13505.FStar_TypeChecker_Env.implicits)
                                     } in
                                   let uu____13506 =
                                     let g' =
                                       FStar_TypeChecker_Rel.teq env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t in
                                     let g2 =
                                       FStar_TypeChecker_Rel.conj_guard g1 g' in
                                     let env13 =
                                       FStar_TypeChecker_Env.set_range env12
                                         exp1.FStar_Syntax_Syntax.pos in
                                     let uu____13510 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         env13 g2 in
                                     FStar_All.pipe_right uu____13510
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1 in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____13527 =
                                       let uu____13528 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____13528 in
                                     if uu____13527
                                     then
                                       let unresolved =
                                         let uu____13540 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____13540
                                           FStar_Util.set_elements in
                                       let uu____13567 =
                                         let uu____13568 =
                                           let uu____13573 =
                                             let uu____13574 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____13575 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____13576 =
                                               let uu____13577 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____13595  ->
                                                         match uu____13595
                                                         with
                                                         | (u,uu____13601) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____13577
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____13574 uu____13575
                                               uu____13576 in
                                           (uu____13573,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____13568 in
                                       raise uu____13567
                                     else ());
                                    (let uu____13606 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____13606
                                     then
                                       let uu____13607 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____13607
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____13618 =
                   let uu____13625 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____13625
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____13618 with
                  | (scrutinee_env,uu____13649) ->
                      let uu____13654 = tc_pat true pat_t pattern in
                      (match uu____13654 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____13692 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____13720 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____13720
                                 then
                                   raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____13734 =
                                      let uu____13741 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool in
                                      tc_term uu____13741 e in
                                    match uu____13734 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g)) in
                           (match uu____13692 with
                            | (when_clause1,g_when) ->
                                let uu____13775 = tc_term pat_env branch_exp in
                                (match uu____13775 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some w ->
                                           let uu____13807 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_40  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_40) uu____13807 in
                                     let uu____13810 =
                                       let eqs =
                                         let uu____13820 =
                                           let uu____13821 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____13821 in
                                         if uu____13820
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____13828 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____13849 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____13850 ->
                                                FStar_Pervasives_Native.None
                                            | uu____13851 ->
                                                let uu____13852 =
                                                  let uu____13853 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____13853 pat_t
                                                    scrutinee_tm e in
                                                FStar_Pervasives_Native.Some
                                                  uu____13852) in
                                       let uu____13854 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch in
                                       match uu____13854 with
                                       | (c1,g_branch1) ->
                                           let uu____13869 =
                                             match (eqs, when_condition) with
                                             | uu____13882 when
                                                 let uu____13891 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation
                                                   uu____13891
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
                                                 let uu____13903 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____13904 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____13903, uu____13904)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____13913 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____13913 in
                                                 let uu____13914 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____13915 =
                                                   let uu____13916 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____13916 g_when in
                                                 (uu____13914, uu____13915)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____13924 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____13924, g_when) in
                                           (match uu____13869 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____13936 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____13937 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____13936, uu____13937,
                                                  g_branch1)) in
                                     (match uu____13810 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____13958 =
                                              let uu____13959 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____13959 in
                                            if uu____13958
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____13993 =
                                                     let uu____13994 =
                                                       let uu____13995 =
                                                         let uu____13998 =
                                                           let uu____14005 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____14005 in
                                                         FStar_Pervasives_Native.snd
                                                           uu____13998 in
                                                       FStar_List.length
                                                         uu____13995 in
                                                     uu____13994 >
                                                       (Prims.parse_int "1") in
                                                   if uu____13993
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____14011 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____14011 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____14032 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None in
                                                         let disc1 =
                                                           let uu____14049 =
                                                             let uu____14050
                                                               =
                                                               let uu____14051
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____14051] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____14050 in
                                                           uu____14049
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____14054 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool in
                                                         [uu____14054]
                                                   else [] in
                                                 let fail uu____14059 =
                                                   let uu____14060 =
                                                     let uu____14061 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____14062 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____14063 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____14061
                                                       uu____14062
                                                       uu____14063 in
                                                   failwith uu____14060 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____14078) ->
                                                       head_constructor t1
                                                   | uu____14087 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____14089 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____14089
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____14092 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____14113;
                                                        FStar_Syntax_Syntax.tk
                                                          = uu____14114;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____14115;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____14116;_},uu____14117)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____14166 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____14168 =
                                                       let uu____14169 =
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____14169
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____14168]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____14170 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____14180 =
                                                       let uu____14181 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____14181 in
                                                     if uu____14180
                                                     then []
                                                     else
                                                       (let uu____14185 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____14185)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____14188 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____14190 =
                                                       let uu____14191 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____14191 in
                                                     if uu____14190
                                                     then []
                                                     else
                                                       (let uu____14195 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____14195)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____14229 =
                                                       let uu____14230 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____14230 in
                                                     if uu____14229
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____14237 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____14273
                                                                     ->
                                                                    match uu____14273
                                                                    with
                                                                    | 
                                                                    (ei,uu____14285)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____14295
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____14295
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____14316
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____14332
                                                                    =
                                                                    let uu____14333
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____14334
                                                                    =
                                                                    let uu____14335
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____14335] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____14333
                                                                    uu____14334 in
                                                                    uu____14332
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____14237
                                                            FStar_List.flatten in
                                                        let uu____14344 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____14344
                                                          sub_term_guards)
                                                 | uu____14347 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____14363 =
                                                   let uu____14364 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____14364 in
                                                 if uu____14363
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____14367 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____14367 in
                                                    let uu____14372 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____14372 with
                                                    | (k,uu____14378) ->
                                                        let uu____14379 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____14379
                                                         with
                                                         | (t1,uu____14387,uu____14388)
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
                                              g_when1 g_branch1 in
                                          ((let uu____14394 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____14394
                                            then
                                              let uu____14395 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____14395
                                            else ());
                                           (let uu____14397 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____14397, branch_guard, c1,
                                              guard)))))))))
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
          let uu____14427 = check_let_bound_def true env1 lb in
          (match uu____14427 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____14449 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____14466 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____14466, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____14469 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____14469
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____14473 =
                      let uu____14482 =
                        let uu____14493 =
                          let uu____14502 =
                            let uu____14517 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____14517) in
                          [uu____14502] in
                        FStar_TypeChecker_Util.generalize env1 uu____14493 in
                      FStar_List.hd uu____14482 in
                    match uu____14473 with
                    | (uu____14574,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____14449 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____14588 =
                      let uu____14597 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____14597
                      then
                        let uu____14606 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____14606 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____14635 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____14635
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____14636 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____14636, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____14652 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____14652
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1) in
                          let e21 =
                            let uu____14666 =
                              FStar_Syntax_Util.is_pure_comp c in
                            if uu____14666
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
                    (match uu____14588 with
                     | (e21,c12) ->
                         let cres =
                           FStar_TypeChecker_Env.null_wp_for_eff env1
                             (FStar_Syntax_Util.comp_effect_name c12)
                             FStar_Syntax_Syntax.U_zero
                             FStar_TypeChecker_Common.t_unit in
                         (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                            (FStar_Pervasives_Native.Some
                               (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                          (let lb1 =
                             FStar_Syntax_Util.close_univs_and_mk_letbinding
                               FStar_Pervasives_Native.None
                               lb.FStar_Syntax_Syntax.lbname univ_vars2
                               (FStar_Syntax_Util.comp_result c12)
                               (FStar_Syntax_Util.comp_effect_name c12) e11 in
                           let uu____14703 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_let
                                  ((false, [lb1]), e21))
                               (FStar_Pervasives_Native.Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos in
                           (uu____14703,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____14724 -> failwith "Impossible"
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
            let uu___114_14759 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___114_14759.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___114_14759.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___114_14759.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___114_14759.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___114_14759.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___114_14759.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___114_14759.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___114_14759.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___114_14759.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___114_14759.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___114_14759.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___114_14759.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___114_14759.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___114_14759.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___114_14759.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___114_14759.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___114_14759.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___114_14759.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___114_14759.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___114_14759.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___114_14759.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___114_14759.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___114_14759.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___114_14759.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___114_14759.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___114_14759.FStar_TypeChecker_Env.is_native_tactic)
            } in
          let uu____14760 =
            let uu____14771 =
              let uu____14772 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____14772 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____14771 lb in
          (match uu____14760 with
           | (e1,uu____14794,c1,g1,annotated) ->
               let x =
                 let uu___115_14799 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___115_14799.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___115_14799.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____14800 =
                 let uu____14805 =
                   let uu____14806 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____14806] in
                 FStar_Syntax_Subst.open_term uu____14805 e2 in
               (match uu____14800 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = FStar_Pervasives_Native.fst xbinder in
                    let uu____14825 =
                      let uu____14832 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____14832 e21 in
                    (match uu____14825 with
                     | (e22,c2,g2) ->
                         let cres =
                           FStar_TypeChecker_Util.bind
                             e1.FStar_Syntax_Syntax.pos env2
                             (FStar_Pervasives_Native.Some e1) c1
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
                           let uu____14853 =
                             let uu____14858 =
                               let uu____14859 =
                                 let uu____14874 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____14874) in
                               FStar_Syntax_Syntax.Tm_let uu____14859 in
                             FStar_Syntax_Syntax.mk uu____14858 in
                           uu____14853
                             (FStar_Pervasives_Native.Some
                                ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____14889 =
                             let uu____14890 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____14891 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____14890
                               c1.FStar_Syntax_Syntax.res_typ uu____14891 e11 in
                           FStar_All.pipe_left
                             (fun _0_41  ->
                                FStar_TypeChecker_Common.NonTrivial _0_41)
                             uu____14889 in
                         let g21 =
                           let uu____14893 =
                             let uu____14894 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____14894 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____14893 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____14896 =
                           let uu____14897 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____14897 in
                         if uu____14896
                         then
                           let tt =
                             let uu____14907 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____14907
                               FStar_Option.get in
                           ((let uu____14913 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____14913
                             then
                               let uu____14914 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____14915 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____14914 uu____14915
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape FStar_Pervasives_Native.None
                                env2 [x1] cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____14920 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____14920
                             then
                               let uu____14921 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____14922 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____14921 uu____14922
                             else ());
                            (e4,
                              ((let uu___116_14925 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___116_14925.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___116_14925.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___116_14925.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____14926 -> failwith "Impossible"
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
          let uu____14962 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____14962 with
           | (lbs1,e21) ->
               let uu____14981 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____14981 with
                | (env0,topt) ->
                    let uu____15000 = build_let_rec_env true env0 lbs1 in
                    (match uu____15000 with
                     | (lbs2,rec_env) ->
                         let uu____15019 = check_let_recs rec_env lbs2 in
                         (match uu____15019 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____15039 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____15039
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____15045 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____15045
                                  (fun _0_42  ->
                                     FStar_Pervasives_Native.Some _0_42) in
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
                                     let uu____15090 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____15134 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____15134))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____15090 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____15178  ->
                                           match uu____15178 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____15222 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____15222 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (FStar_Pervasives_Native.Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____15234 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                                match uu____15234 with
                                | (lbs5,e22) ->
                                    ((let uu____15254 =
                                        FStar_TypeChecker_Rel.discharge_guard
                                          env1 g_lbs1 in
                                      FStar_All.pipe_right uu____15254
                                        (FStar_TypeChecker_Rel.force_trivial_guard
                                           env1));
                                     (let uu____15255 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs5), e22))
                                          (FStar_Pervasives_Native.Some
                                             (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                          top.FStar_Syntax_Syntax.pos in
                                      (uu____15255, cres,
                                        FStar_TypeChecker_Rel.trivial_guard)))))))))
      | uu____15272 -> failwith "Impossible"
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
          let uu____15308 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____15308 with
           | (lbs1,e21) ->
               let uu____15327 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____15327 with
                | (env0,topt) ->
                    let uu____15346 = build_let_rec_env false env0 lbs1 in
                    (match uu____15346 with
                     | (lbs2,rec_env) ->
                         let uu____15365 = check_let_recs rec_env lbs2 in
                         (match uu____15365 with
                          | (lbs3,g_lbs) ->
                              let uu____15384 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___117_15407 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___117_15407.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___117_15407.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___118_15409 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___118_15409.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___118_15409.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___118_15409.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___118_15409.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____15384 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____15438 = tc_term env2 e21 in
                                   (match uu____15438 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____15455 =
                                            let uu____15456 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____15456 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____15455 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___119_15460 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___119_15460.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___119_15460.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___119_15460.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____15461 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____15461 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 (FStar_Pervasives_Native.Some
                                                    (tres.FStar_Syntax_Syntax.n))
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____15499 ->
                                                  (e, cres2, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  let cres3 =
                                                    let uu___120_15506 =
                                                      cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___120_15506.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___120_15506.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___120_15506.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____15511 -> failwith "Impossible"
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
          let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp in
          let uu____15541 =
            let uu____15546 =
              let uu____15547 = FStar_Syntax_Subst.compress t in
              uu____15547.FStar_Syntax_Syntax.n in
            let uu____15552 =
              let uu____15553 = FStar_Syntax_Subst.compress lbdef in
              uu____15553.FStar_Syntax_Syntax.n in
            (uu____15546, uu____15552) in
          match uu____15541 with
          | (FStar_Syntax_Syntax.Tm_arrow
             (formals,c),FStar_Syntax_Syntax.Tm_abs
             (actuals,uu____15561,uu____15562)) ->
              let actuals1 =
                let uu____15608 =
                  FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                FStar_TypeChecker_Util.maybe_add_implicit_binders uu____15608
                  actuals in
              (if (FStar_List.length formals) <> (FStar_List.length actuals1)
               then
                 (let actuals_msg =
                    let n1 = FStar_List.length actuals1 in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument was found"
                    else
                      (let uu____15629 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments were found"
                         uu____15629) in
                  let formals_msg =
                    let n1 = FStar_List.length formals in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument"
                    else
                      (let uu____15647 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments" uu____15647) in
                  let msg =
                    let uu____15655 = FStar_Syntax_Print.term_to_string lbtyp in
                    let uu____15656 =
                      FStar_Syntax_Print.lbname_to_string lbname in
                    FStar_Util.format4
                      "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                      uu____15655 uu____15656 formals_msg actuals_msg in
                  raise
                    (FStar_Errors.Error
                       (msg, (lbdef.FStar_Syntax_Syntax.pos))))
               else ();
               (let quals =
                  FStar_TypeChecker_Env.lookup_effect_quals env
                    (FStar_Syntax_Util.comp_effect_name c) in
                FStar_All.pipe_right quals
                  (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
          | uu____15663 ->
              let uu____15668 =
                let uu____15669 =
                  let uu____15674 =
                    let uu____15675 = FStar_Syntax_Print.term_to_string lbdef in
                    let uu____15676 = FStar_Syntax_Print.term_to_string lbtyp in
                    FStar_Util.format2
                      "Only function literals with arrow types can be defined recursively; got %s : %s"
                      uu____15675 uu____15676 in
                  (uu____15674, (lbtyp.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____15669 in
              raise uu____15668 in
        let uu____15677 =
          FStar_List.fold_left
            (fun uu____15703  ->
               fun lb  ->
                 match uu____15703 with
                 | (lbs1,env1) ->
                     let uu____15723 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____15723 with
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
                              (let uu____15743 =
                                 let uu____15750 =
                                   let uu____15751 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____15751 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___121_15762 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___121_15762.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___121_15762.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___121_15762.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___121_15762.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___121_15762.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___121_15762.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___121_15762.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___121_15762.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___121_15762.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___121_15762.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___121_15762.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___121_15762.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___121_15762.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___121_15762.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___121_15762.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___121_15762.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___121_15762.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___121_15762.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___121_15762.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___121_15762.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___121_15762.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___121_15762.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___121_15762.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___121_15762.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___121_15762.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___121_15762.FStar_TypeChecker_Env.is_native_tactic)
                                    }) t uu____15750 in
                               match uu____15743 with
                               | (t1,uu____15764,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____15768 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____15768);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____15770 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____15770
                            then
                              let uu___122_15771 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___122_15771.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___122_15771.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___122_15771.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___122_15771.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___122_15771.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___122_15771.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___122_15771.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___122_15771.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___122_15771.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___122_15771.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___122_15771.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___122_15771.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___122_15771.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___122_15771.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___122_15771.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___122_15771.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___122_15771.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___122_15771.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___122_15771.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___122_15771.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___122_15771.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___122_15771.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___122_15771.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___122_15771.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___122_15771.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___122_15771.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1) in
                          let lb1 =
                            let uu___123_15788 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___123_15788.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___123_15788.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____15677 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lbs  ->
      let uu____15811 =
        let uu____15820 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____15849 =
                     let uu____15850 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____15850.FStar_Syntax_Syntax.n in
                   match uu____15849 with
                   | FStar_Syntax_Syntax.Tm_abs uu____15855 -> ()
                   | uu____15874 ->
                       let uu____15875 =
                         let uu____15876 =
                           let uu____15881 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____15881) in
                         FStar_Errors.Error uu____15876 in
                       raise uu____15875);
                  (let uu____15882 =
                     let uu____15889 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____15889
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____15882 with
                   | (e,c,g) ->
                       ((let uu____15898 =
                           let uu____15899 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____15899 in
                         if uu____15898
                         then
                           raise
                             (FStar_Errors.Error
                                ("Expected let rec to be a Tot term; got effect GTot",
                                  (e.FStar_Syntax_Syntax.pos)))
                         else ());
                        (let lb1 =
                           FStar_Syntax_Util.mk_letbinding
                             lb.FStar_Syntax_Syntax.lbname
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbtyp
                             FStar_Parser_Const.effect_Tot_lid e in
                         (lb1, g)))))) in
        FStar_All.pipe_right uu____15820 FStar_List.unzip in
      match uu____15811 with
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
        let uu____15948 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____15948 with
        | (env1,uu____15966) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____15976 = check_lbtyp top_level env lb in
            (match uu____15976 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____16020 =
                     tc_maybe_toplevel_term
                       (let uu___124_16029 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___124_16029.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___124_16029.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___124_16029.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___124_16029.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___124_16029.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___124_16029.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___124_16029.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___124_16029.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___124_16029.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___124_16029.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___124_16029.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___124_16029.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___124_16029.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___124_16029.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___124_16029.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___124_16029.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___124_16029.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___124_16029.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___124_16029.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___124_16029.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___124_16029.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___124_16029.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___124_16029.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___124_16029.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___124_16029.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___124_16029.FStar_TypeChecker_Env.is_native_tactic)
                        }) e11 in
                   match uu____16020 with
                   | (e12,c1,g1) ->
                       let uu____16043 =
                         let uu____16048 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____16052  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____16048 e12 c1 wf_annot in
                       (match uu____16043 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____16067 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____16067
                              then
                                let uu____16068 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____16069 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____16070 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____16068 uu____16069 uu____16070
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
            (if lb.FStar_Syntax_Syntax.lbunivs <> []
             then
               failwith
                 "Impossible: non-empty universe variables but the type is unknown"
             else ();
             (FStar_Pervasives_Native.None,
               FStar_TypeChecker_Rel.trivial_guard, [], [], env))
        | uu____16114 ->
            let uu____16115 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____16115 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____16164 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____16164)
                 else
                   (let uu____16172 = FStar_Syntax_Util.type_u () in
                    match uu____16172 with
                    | (k,uu____16192) ->
                        let uu____16193 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____16193 with
                         | (t2,uu____16215,g) ->
                             ((let uu____16218 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____16218
                               then
                                 let uu____16219 =
                                   let uu____16220 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____16220 in
                                 let uu____16221 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____16219 uu____16221
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____16224 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____16224))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun uu____16232  ->
      match uu____16232 with
      | (x,imp) ->
          let uu____16251 = FStar_Syntax_Util.type_u () in
          (match uu____16251 with
           | (tu,u) ->
               ((let uu____16271 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____16271
                 then
                   let uu____16272 = FStar_Syntax_Print.bv_to_string x in
                   let uu____16273 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____16274 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____16272 uu____16273 uu____16274
                 else ());
                (let uu____16276 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____16276 with
                 | (t,uu____16296,g) ->
                     let x1 =
                       ((let uu___125_16304 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___125_16304.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___125_16304.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____16306 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____16306
                       then
                         let uu____16307 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1) in
                         let uu____16308 =
                           FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____16307 uu____16308
                       else ());
                      (let uu____16310 = push_binding env x1 in
                       (x1, uu____16310, g, u))))))
and tc_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_TypeChecker_Env.env,
        FStar_TypeChecker_Env.guard_t,FStar_Syntax_Syntax.universe Prims.list)
        FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun bs  ->
      let rec aux env1 bs1 =
        match bs1 with
        | [] -> ([], env1, FStar_TypeChecker_Rel.trivial_guard, [])
        | b::bs2 ->
            let uu____16400 = tc_binder env1 b in
            (match uu____16400 with
             | (b1,env',g,u) ->
                 let uu____16441 = aux env' bs2 in
                 (match uu____16441 with
                  | (bs3,env'1,g',us) ->
                      let uu____16494 =
                        let uu____16495 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____16495 in
                      ((b1 :: bs3), env'1, uu____16494, (u :: us)))) in
      aux env bs
and tc_pats:
  FStar_TypeChecker_Env.env ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
       FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
      (FStar_Syntax_Syntax.args Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pats  ->
      let tc_args env1 args =
        FStar_List.fold_right
          (fun uu____16582  ->
             fun uu____16583  ->
               match (uu____16582, uu____16583) with
               | ((t,imp),(args1,g)) ->
                   let uu____16652 = tc_term env1 t in
                   (match uu____16652 with
                    | (t1,uu____16670,g') ->
                        let uu____16672 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____16672))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____16714  ->
             match uu____16714 with
             | (pats1,g) ->
                 let uu____16739 = tc_args env p in
                 (match uu____16739 with
                  | (args,g') ->
                      let uu____16752 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____16752))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let uu____16765 = tc_maybe_toplevel_term env e in
      match uu____16765 with
      | (e1,c,g) ->
          let uu____16781 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____16781
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____16796 =
               let uu____16801 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____16801
               then
                 let uu____16806 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____16806, false)
               else
                 (let uu____16808 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____16808, true)) in
             match uu____16796 with
             | (target_comp,allow_ghost) ->
                 let uu____16817 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____16817 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____16827 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____16827)
                  | uu____16828 ->
                      if allow_ghost
                      then
                        let uu____16837 =
                          let uu____16838 =
                            let uu____16843 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____16843, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____16838 in
                        raise uu____16837
                      else
                        (let uu____16851 =
                           let uu____16852 =
                             let uu____16857 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____16857, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____16852 in
                         raise uu____16851)))
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
      let uu____16876 = tc_tot_or_gtot_term env t in
      match uu____16876 with
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
      (let uu____16906 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____16906
       then
         let uu____16907 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____16907
       else ());
      (let env1 =
         let uu___126_16910 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___126_16910.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___126_16910.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___126_16910.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___126_16910.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___126_16910.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___126_16910.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___126_16910.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___126_16910.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___126_16910.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___126_16910.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___126_16910.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___126_16910.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___126_16910.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___126_16910.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___126_16910.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___126_16910.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___126_16910.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___126_16910.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___126_16910.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___126_16910.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___126_16910.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___126_16910.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___126_16910.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___126_16910.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___126_16910.FStar_TypeChecker_Env.is_native_tactic)
         } in
       let uu____16915 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____16948) ->
             let uu____16949 =
               let uu____16950 =
                 let uu____16955 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____16955) in
               FStar_Errors.Error uu____16950 in
             raise uu____16949 in
       match uu____16915 with
       | (t,c,g) ->
           let uu____16971 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____16971
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____16983 =
                let uu____16984 =
                  let uu____16989 =
                    let uu____16990 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____16990 in
                  let uu____16991 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____16989, uu____16991) in
                FStar_Errors.Error uu____16984 in
              raise uu____16983))
let level_of_type_fail env e t =
  let uu____17019 =
    let uu____17020 =
      let uu____17025 =
        let uu____17026 = FStar_Syntax_Print.term_to_string e in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____17026 t in
      let uu____17027 = FStar_TypeChecker_Env.get_range env in
      (uu____17025, uu____17027) in
    FStar_Errors.Error uu____17020 in
  raise uu____17019
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____17047 =
            let uu____17048 = FStar_Syntax_Util.unrefine t1 in
            uu____17048.FStar_Syntax_Syntax.n in
          match uu____17047 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____17054 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____17057 = FStar_Syntax_Util.type_u () in
                 match uu____17057 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___129_17065 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___129_17065.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___129_17065.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___129_17065.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___129_17065.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___129_17065.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___129_17065.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___129_17065.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___129_17065.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___129_17065.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___129_17065.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___129_17065.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___129_17065.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___129_17065.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___129_17065.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___129_17065.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___129_17065.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___129_17065.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___129_17065.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___129_17065.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___129_17065.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___129_17065.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___129_17065.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___129_17065.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___129_17065.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___129_17065.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___129_17065.FStar_TypeChecker_Env.is_native_tactic)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____17069 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____17069
                       | uu____17070 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u)) in
        aux true t
let rec universe_of_aux:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun e  ->
      let uu____17083 =
        let uu____17084 = FStar_Syntax_Subst.compress e in
        uu____17084.FStar_Syntax_Syntax.n in
      match uu____17083 with
      | FStar_Syntax_Syntax.Tm_bvar uu____17093 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____17102 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____17135 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____17153) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____17182,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____17217) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____17228 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____17228 with | ((uu____17241,t),uu____17243) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____17248,(FStar_Util.Inl t,uu____17250),uu____17251) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____17322,(FStar_Util.Inr c,uu____17324),uu____17325) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____17399;
             FStar_Syntax_Syntax.pos = uu____17400;
             FStar_Syntax_Syntax.vars = uu____17401;_},us)
          ->
          let uu____17411 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____17411 with
           | ((us',t),uu____17426) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____17432 =
                     let uu____17433 =
                       let uu____17438 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____17438) in
                     FStar_Errors.Error uu____17433 in
                   raise uu____17432)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____17454 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____17455 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____17469) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____17500 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____17500 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____17522  ->
                      match uu____17522 with
                      | (b,uu____17528) ->
                          let uu____17529 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____17529) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____17536 = universe_of_aux env res in
                 level_of_type env res uu____17536 in
               let u_c =
                 let uu____17538 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____17538 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____17542 = universe_of_aux env trepr in
                     level_of_type env trepr uu____17542 in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____17659 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____17678 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____17725 ->
                let uu____17726 = universe_of_aux env hd3 in
                (uu____17726, args1)
            | FStar_Syntax_Syntax.Tm_name uu____17745 ->
                let uu____17746 = universe_of_aux env hd3 in
                (uu____17746, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____17765 ->
                let uu____17786 = universe_of_aux env hd3 in
                (uu____17786, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____17805 ->
                let uu____17814 = universe_of_aux env hd3 in
                (uu____17814, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____17833 ->
                let uu____17868 = universe_of_aux env hd3 in
                (uu____17868, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____17887 ->
                let uu____17896 = universe_of_aux env hd3 in
                (uu____17896, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____17915 ->
                let uu____17916 = universe_of_aux env hd3 in
                (uu____17916, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____17935 ->
                let uu____17950 = universe_of_aux env hd3 in
                (uu____17950, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____17969 ->
                let uu____17978 = universe_of_aux env hd3 in
                (uu____17978, args1)
            | FStar_Syntax_Syntax.Tm_type uu____17997 ->
                let uu____17998 = universe_of_aux env hd3 in
                (uu____17998, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____18017,hd4::uu____18019) ->
                let uu____18104 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____18104 with
                 | (uu____18123,uu____18124,hd5) ->
                     let uu____18150 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____18150 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____18217 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____18219 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____18219 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____18286 ->
                let uu____18287 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____18287 with
                 | (env1,uu____18313) ->
                     let env2 =
                       let uu___130_18319 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___130_18319.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___130_18319.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___130_18319.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___130_18319.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___130_18319.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___130_18319.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___130_18319.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___130_18319.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___130_18319.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___130_18319.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___130_18319.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___130_18319.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___130_18319.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___130_18319.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___130_18319.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___130_18319.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___130_18319.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___130_18319.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___130_18319.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___130_18319.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___130_18319.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___130_18319.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___130_18319.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___130_18319.FStar_TypeChecker_Env.is_native_tactic)
                       } in
                     ((let uu____18321 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____18321
                       then
                         let uu____18322 =
                           let uu____18323 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____18323 in
                         let uu____18324 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____18322 uu____18324
                       else ());
                      (let uu____18326 = tc_term env2 hd3 in
                       match uu____18326 with
                       | (uu____18351,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____18352;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____18354;
                                        FStar_Syntax_Syntax.comp =
                                          uu____18355;_},g)
                           ->
                           ((let uu____18370 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____18370
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____18385 = type_of_head true hd1 args in
          (match uu____18385 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____18439 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____18439 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____18491 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____18491)))
      | FStar_Syntax_Syntax.Tm_match (uu____18496,hd1::uu____18498) ->
          let uu____18583 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____18583 with
           | (uu____18588,uu____18589,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____18615,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____18674 = universe_of_aux env e in
      level_of_type env e uu____18674
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tps  ->
      let uu____18695 = tc_binders env tps in
      match uu____18695 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))