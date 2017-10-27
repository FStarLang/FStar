open Prims
let instantiate_both: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___119_5 = env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___119_5.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___119_5.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___119_5.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___119_5.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___119_5.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___119_5.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___119_5.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___119_5.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___119_5.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___119_5.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___119_5.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___119_5.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___119_5.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___119_5.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___119_5.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___119_5.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___119_5.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___119_5.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___119_5.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___119_5.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___119_5.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___119_5.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___119_5.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___119_5.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___119_5.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___119_5.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___119_5.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___119_5.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___119_5.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___119_5.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___119_5.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___119_5.FStar_TypeChecker_Env.dsenv)
    }
let no_inst: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___120_10 = env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___120_10.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___120_10.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___120_10.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___120_10.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___120_10.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___120_10.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___120_10.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___120_10.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___120_10.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___120_10.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___120_10.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___120_10.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___120_10.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___120_10.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___120_10.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___120_10.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___120_10.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___120_10.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___120_10.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___120_10.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___120_10.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___120_10.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___120_10.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___120_10.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___120_10.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___120_10.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___120_10.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___120_10.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___120_10.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___120_10.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___120_10.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___120_10.FStar_TypeChecker_Env.dsenv)
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
           let uu____43 =
             let uu____44 =
               let uu____45 = FStar_Syntax_Syntax.as_arg v1 in
               let uu____46 =
                 let uu____49 = FStar_Syntax_Syntax.as_arg tl1 in [uu____49] in
               uu____45 :: uu____46 in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____44 in
           uu____43 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
let is_eq:
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___114_57  ->
    match uu___114_57 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____60 -> false
let steps:
  'Auu____67 . 'Auu____67 -> FStar_TypeChecker_Normalize.step Prims.list =
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
            | uu____121 ->
                let t1 = if try_norm then norm env t else t in
                let fvs' = FStar_Syntax_Free.names t1 in
                let uu____129 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs in
                (match uu____129 with
                 | FStar_Pervasives_Native.None  -> t1
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____139 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____141 =
                                  FStar_Syntax_Print.bv_to_string x in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____141
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____143 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____144 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1 in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____143 uu____144 in
                          let uu____145 =
                            let uu____146 =
                              let uu____151 =
                                FStar_TypeChecker_Env.get_range env in
                              (msg, uu____151) in
                            FStar_Errors.Error uu____146 in
                          FStar_Exn.raise uu____145 in
                        let s =
                          let uu____153 =
                            let uu____154 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____154 in
                          FStar_TypeChecker_Util.new_uvar env uu____153 in
                        let uu____163 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s in
                        match uu____163 with
                        | FStar_Pervasives_Native.Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____168 -> fail ())) in
          aux false kt
let push_binding:
  'Auu____177 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____177) FStar_Pervasives_Native.tuple2 ->
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
        let uu____210 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____210
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v1))
          :: s
let set_lcomp_result:
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___121_226 = lc in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___121_226.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags =
          (uu___121_226.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____229  ->
             let uu____230 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Util.set_result_typ uu____230 t)
      }
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
          let should_return t =
            let uu____281 =
              let uu____282 = FStar_Syntax_Subst.compress t in
              uu____282.FStar_Syntax_Syntax.n in
            match uu____281 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____285,c) ->
                let uu____303 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c) in
                if uu____303
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c) in
                  let uu____305 =
                    let uu____306 = FStar_Syntax_Subst.compress t1 in
                    uu____306.FStar_Syntax_Syntax.n in
                  (match uu____305 with
                   | FStar_Syntax_Syntax.Tm_constant uu____309 -> false
                   | uu____310 ->
                       let uu____311 = FStar_Syntax_Util.is_unit t1 in
                       Prims.op_Negation uu____311)
                else false
            | uu____313 ->
                let uu____314 = FStar_Syntax_Util.is_unit t in
                Prims.op_Negation uu____314 in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____317 =
                  let uu____320 =
                    (let uu____323 = should_return t in
                     Prims.op_Negation uu____323) ||
                      (let uu____325 =
                         FStar_TypeChecker_Env.should_verify env in
                       Prims.op_Negation uu____325) in
                  if uu____320
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e in
                FStar_Syntax_Util.lcomp_of_comp uu____317
            | FStar_Util.Inr lc -> lc in
          let t = lc.FStar_Syntax_Syntax.res_typ in
          let uu____333 =
            let uu____340 = FStar_TypeChecker_Env.expected_typ env in
            match uu____340 with
            | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                ((let uu____351 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High in
                  if uu____351
                  then
                    let uu____352 = FStar_Syntax_Print.term_to_string t in
                    let uu____353 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____352
                      uu____353
                  else ());
                 (let uu____355 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t' in
                  match uu____355 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____371 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____371 with
                       | (e2,g) ->
                           ((let uu____385 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____385
                             then
                               let uu____386 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____387 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____388 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____389 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____386 uu____387 uu____388 uu____389
                             else ());
                            (let msg =
                               let uu____396 =
                                 FStar_TypeChecker_Rel.is_trivial g in
                               if uu____396
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_40  ->
                                      FStar_Pervasives_Native.Some _0_40)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             let uu____413 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1 in
                             match uu____413 with
                             | (lc2,g2) ->
                                 ((memo_tk e2 t'), (set_lcomp_result lc2 t'),
                                   g2)))))) in
          match uu____333 with
          | (e1,lc1,g) ->
              ((let uu____436 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low in
                if uu____436
                then
                  let uu____437 = FStar_Syntax_Print.lcomp_to_string lc1 in
                  FStar_Util.print1 "Return comp type is %s\n" uu____437
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
        let uu____463 = FStar_TypeChecker_Env.expected_typ env in
        match uu____463 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____473 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____473 with
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
      fun uu____509  ->
        match uu____509 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____538 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____538
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____540 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____540
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____542 =
              match copt with
              | FStar_Pervasives_Native.Some uu____555 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____558 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____560 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____560)) in
                  if uu____558
                  then
                    let uu____567 =
                      let uu____570 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos in
                      FStar_Pervasives_Native.Some uu____570 in
                    (uu____567, c)
                  else
                    (let uu____574 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____574
                     then
                       let uu____581 = tot_or_gtot c in
                       (FStar_Pervasives_Native.None, uu____581)
                     else
                       (let uu____585 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____585
                        then
                          let uu____592 =
                            let uu____595 = tot_or_gtot c in
                            FStar_Pervasives_Native.Some uu____595 in
                          (uu____592, c)
                        else (FStar_Pervasives_Native.None, c))) in
            (match uu____542 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let uu____621 =
                        FStar_TypeChecker_Util.check_comp env e c2 expected_c in
                      (match uu____621 with
                       | (e1,uu____635,g) ->
                           let g1 =
                             let uu____638 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_TypeChecker_Util.label_guard uu____638
                               "could not prove post-condition" g in
                           ((let uu____640 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low in
                             if uu____640
                             then
                               let uu____641 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos in
                               let uu____642 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1 in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____641 uu____642
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c2)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c2) in
                             (e2, expected_c, g1))))))
let no_logical_guard:
  'Auu____653 'Auu____654 .
    FStar_TypeChecker_Env.env ->
      ('Auu____654,'Auu____653,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____654,'Auu____653,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____674  ->
      match uu____674 with
      | (te,kt,f) ->
          let uu____684 = FStar_TypeChecker_Rel.guard_form f in
          (match uu____684 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____692 =
                 let uu____693 =
                   let uu____698 =
                     FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                       env f1 in
                   let uu____699 = FStar_TypeChecker_Env.get_range env in
                   (uu____698, uu____699) in
                 FStar_Errors.Error uu____693 in
               FStar_Exn.raise uu____692)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____710 = FStar_TypeChecker_Env.expected_typ env in
    match uu____710 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____714 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____714
let rec get_pat_vars:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun pats  ->
    fun acc  ->
      let pats1 = FStar_Syntax_Util.unmeta pats in
      let uu____738 = FStar_Syntax_Util.head_and_args pats1 in
      match uu____738 with
      | (head1,args) ->
          let uu____777 =
            let uu____778 = FStar_Syntax_Util.un_uinst head1 in
            uu____778.FStar_Syntax_Syntax.n in
          (match uu____777 with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid
               ->
               let uu____785 = FStar_List.tl args in
               get_pat_vars_args uu____785 acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.smtpatOr_lid
               -> get_pat_vars_args args acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               -> get_pat_vars_args args acc
           | uu____794 ->
               let uu____795 = FStar_Syntax_Free.names pats1 in
               FStar_Util.set_union acc uu____795)
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
  'Auu____830 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,'Auu____830) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____863 = FStar_Syntax_Util.is_smt_lemma t in
          if uu____863
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____864;
                  FStar_Syntax_Syntax.effect_name = uu____865;
                  FStar_Syntax_Syntax.result_typ = uu____866;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____870)::[];
                  FStar_Syntax_Syntax.flags = uu____871;_}
                ->
                let pat_vars =
                  let uu____919 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta] env pats in
                  let uu____920 =
                    FStar_Util.new_set FStar_Syntax_Syntax.order_bv in
                  get_pat_vars uu____919 uu____920 in
                let uu____923 =
                  FStar_All.pipe_right bs
                    (FStar_Util.find_opt
                       (fun uu____950  ->
                          match uu____950 with
                          | (b,uu____956) ->
                              let uu____957 = FStar_Util.set_mem b pat_vars in
                              Prims.op_Negation uu____957)) in
                (match uu____923 with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some (x,uu____963) ->
                     let uu____968 =
                       let uu____969 = FStar_Syntax_Print.bv_to_string x in
                       FStar_Util.format1
                         "Pattern misses at least one bound variable: %s"
                         uu____969 in
                     FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____968)
            | uu____970 -> failwith "Impossible"
          else ()
let guard_letrecs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        let uu____1000 =
          let uu____1001 = FStar_TypeChecker_Env.should_verify env in
          Prims.op_Negation uu____1001 in
        if uu____1000
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env in
               let env1 =
                 let uu___122_1032 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___122_1032.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___122_1032.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___122_1032.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___122_1032.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___122_1032.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___122_1032.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___122_1032.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___122_1032.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___122_1032.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___122_1032.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___122_1032.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___122_1032.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___122_1032.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___122_1032.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___122_1032.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___122_1032.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___122_1032.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___122_1032.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___122_1032.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___122_1032.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___122_1032.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___122_1032.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___122_1032.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___122_1032.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___122_1032.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___122_1032.FStar_TypeChecker_Env.qname_and_index);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___122_1032.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth =
                     (uu___122_1032.FStar_TypeChecker_Env.synth);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___122_1032.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___122_1032.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___122_1032.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___122_1032.FStar_TypeChecker_Env.dsenv)
                 } in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Parser_Const.precedes_lid in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____1066  ->
                           match uu____1066 with
                           | (b,uu____1074) ->
                               let t =
                                 let uu____1076 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort in
                                 FStar_TypeChecker_Normalize.unfold_whnf env1
                                   uu____1076 in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type uu____1079 ->
                                    []
                                | FStar_Syntax_Syntax.Tm_arrow uu____1080 ->
                                    []
                                | uu____1093 ->
                                    let uu____1094 =
                                      FStar_Syntax_Syntax.bv_to_name b in
                                    [uu____1094]))) in
                 let as_lex_list dec =
                   let uu____1099 = FStar_Syntax_Util.head_and_args dec in
                   match uu____1099 with
                   | (head1,uu____1115) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.lexcons_lid
                            -> dec
                        | uu____1137 -> mk_lex_list [dec]) in
                 let cflags = FStar_Syntax_Util.comp_flags c in
                 let uu____1141 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___115_1150  ->
                           match uu___115_1150 with
                           | FStar_Syntax_Syntax.DECREASES uu____1151 -> true
                           | uu____1154 -> false)) in
                 match uu____1141 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.DECREASES dec) -> as_lex_list dec
                 | uu____1158 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions in
                     (match xs with
                      | x::[] -> x
                      | uu____1167 -> mk_lex_list xs) in
               let previous_dec = decreases_clause actuals expected_c in
               let guard_one_letrec uu____1184 =
                 match uu____1184 with
                 | (l,t) ->
                     let uu____1197 =
                       let uu____1198 = FStar_Syntax_Subst.compress t in
                       uu____1198.FStar_Syntax_Syntax.n in
                     (match uu____1197 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____1257  ->
                                    match uu____1257 with
                                    | (x,imp) ->
                                        let uu____1268 =
                                          FStar_Syntax_Syntax.is_null_bv x in
                                        if uu____1268
                                        then
                                          let uu____1273 =
                                            let uu____1274 =
                                              let uu____1277 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x in
                                              FStar_Pervasives_Native.Some
                                                uu____1277 in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____1274
                                              x.FStar_Syntax_Syntax.sort in
                                          (uu____1273, imp)
                                        else (x, imp))) in
                          let uu____1279 =
                            FStar_Syntax_Subst.open_comp formals1 c in
                          (match uu____1279 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1 in
                               let precedes1 =
                                 let uu____1296 =
                                   let uu____1297 =
                                     let uu____1298 =
                                       FStar_Syntax_Syntax.as_arg dec in
                                     let uu____1299 =
                                       let uu____1302 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec in
                                       [uu____1302] in
                                     uu____1298 :: uu____1299 in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____1297 in
                                 uu____1296 FStar_Pervasives_Native.None r in
                               let uu____1305 = FStar_Util.prefix formals2 in
                               (match uu____1305 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___123_1350 = last1 in
                                      let uu____1351 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1 in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___123_1350.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___123_1350.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____1351
                                      } in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)] in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1 in
                                    ((let uu____1377 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low in
                                      if uu____1377
                                      then
                                        let uu____1378 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l in
                                        let uu____1379 =
                                          FStar_Syntax_Print.term_to_string t in
                                        let uu____1380 =
                                          FStar_Syntax_Print.term_to_string
                                            t' in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____1378 uu____1379 uu____1380
                                      else ());
                                     (l, t'))))
                      | uu____1384 ->
                          FStar_Exn.raise
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
        (let uu___124_1815 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___124_1815.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___124_1815.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___124_1815.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___124_1815.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___124_1815.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___124_1815.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___124_1815.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___124_1815.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___124_1815.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___124_1815.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___124_1815.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___124_1815.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___124_1815.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___124_1815.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___124_1815.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___124_1815.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___124_1815.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___124_1815.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___124_1815.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___124_1815.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___124_1815.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___124_1815.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___124_1815.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___124_1815.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___124_1815.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___124_1815.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___124_1815.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___124_1815.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___124_1815.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___124_1815.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___124_1815.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___124_1815.FStar_TypeChecker_Env.dsenv)
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
      (let uu____1827 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1827
       then
         let uu____1828 =
           let uu____1829 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1829 in
         let uu____1830 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1828 uu____1830
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1839 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1870 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1877 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1894 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1895 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1896 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1897 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1898 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1915 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1928 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1935 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____1936;
              FStar_Syntax_Syntax.vars = uu____1937;_},FStar_Syntax_Syntax.Meta_alien
            (uu____1938,uu____1939,ty))
           ->
           let uu____1949 =
             let uu____1950 = FStar_Syntax_Syntax.mk_Total ty in
             FStar_All.pipe_right uu____1950 FStar_Syntax_Util.lcomp_of_comp in
           (top, uu____1949, FStar_TypeChecker_Rel.trivial_guard)
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1956 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1956 with
            | (e2,c,g) ->
                let g1 =
                  let uu___125_1973 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___125_1973.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___125_1973.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___125_1973.FStar_TypeChecker_Env.implicits)
                  } in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1990 = FStar_Syntax_Util.type_u () in
           (match uu____1990 with
            | (t,u) ->
                let uu____2003 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____2003 with
                 | (e2,c,g) ->
                     let uu____2019 =
                       let uu____2034 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____2034 with
                       | (env2,uu____2056) -> tc_pats env2 pats in
                     (match uu____2019 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___126_2090 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___126_2090.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___126_2090.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___126_2090.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____2091 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____2094 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____2091, c, uu____2094))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____2102 =
             let uu____2103 = FStar_Syntax_Subst.compress e1 in
             uu____2103.FStar_Syntax_Syntax.n in
           (match uu____2102 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____2112,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____2114;
                               FStar_Syntax_Syntax.lbtyp = uu____2115;
                               FStar_Syntax_Syntax.lbeff = uu____2116;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____2141 =
                  let uu____2148 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit in
                  tc_term uu____2148 e11 in
                (match uu____2141 with
                 | (e12,c1,g1) ->
                     let uu____2158 = tc_term env1 e2 in
                     (match uu____2158 with
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
                            let uu____2182 =
                              let uu____2185 =
                                let uu____2186 =
                                  let uu____2199 =
                                    let uu____2206 =
                                      let uu____2209 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13) in
                                      [uu____2209] in
                                    (false, uu____2206) in
                                  (uu____2199, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____2186 in
                              FStar_Syntax_Syntax.mk uu____2185 in
                            uu____2182 FStar_Pervasives_Native.None
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
                          let uu____2231 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____2231)))
            | uu____2234 ->
                let uu____2235 = tc_term env1 e1 in
                (match uu____2235 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2257) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____2274 = tc_term env1 e1 in
           (match uu____2274 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____2298) ->
           let uu____2345 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2345 with
            | (env0,uu____2359) ->
                let uu____2364 = tc_comp env0 expected_c in
                (match uu____2364 with
                 | (expected_c1,uu____2378,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____2383 =
                       let uu____2390 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____2390 e1 in
                     (match uu____2383 with
                      | (e2,c',g') ->
                          let uu____2400 =
                            let uu____2407 =
                              let uu____2412 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____2412) in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____2407 in
                          (match uu____2400 with
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
                                   FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos in
                               let lc =
                                 FStar_Syntax_Util.lcomp_of_comp expected_c2 in
                               let f =
                                 let uu____2467 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____2467 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____2476 =
                                            FStar_Syntax_Util.mk_squash f1 in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____2476) in
                               let uu____2477 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____2477 with
                                | (e5,c,f2) ->
                                    let final_guard =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, final_guard))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____2497) ->
           let uu____2544 = FStar_Syntax_Util.type_u () in
           (match uu____2544 with
            | (k,u) ->
                let uu____2557 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____2557 with
                 | (t1,uu____2571,f) ->
                     let uu____2573 =
                       let uu____2580 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____2580 e1 in
                     (match uu____2573 with
                      | (e2,c,g) ->
                          let uu____2590 =
                            let uu____2595 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____2599  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____2595 e2 c f in
                          (match uu____2590 with
                           | (c1,f1) ->
                               let uu____2608 =
                                 let uu____2615 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2,
                                          ((FStar_Util.Inl t1),
                                            FStar_Pervasives_Native.None),
                                          (FStar_Pervasives_Native.Some
                                             (c1.FStar_Syntax_Syntax.eff_name))))
                                     FStar_Pervasives_Native.None
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____2615 c1 in
                               (match uu____2608 with
                                | (e3,c2,f2) ->
                                    let uu____2655 =
                                      let uu____2656 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____2656 in
                                    (e3, c2, uu____2655))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____2657;
              FStar_Syntax_Syntax.vars = uu____2658;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2721 = FStar_Syntax_Util.head_and_args top in
           (match uu____2721 with
            | (unary_op,uu____2743) ->
                let head1 =
                  let uu____2767 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2767 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____2805;
              FStar_Syntax_Syntax.vars = uu____2806;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2869 = FStar_Syntax_Util.head_and_args top in
           (match uu____2869 with
            | (unary_op,uu____2891) ->
                let head1 =
                  let uu____2915 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2915 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____2953);
              FStar_Syntax_Syntax.pos = uu____2954;
              FStar_Syntax_Syntax.vars = uu____2955;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____3018 = FStar_Syntax_Util.head_and_args top in
           (match uu____3018 with
            | (unary_op,uu____3040) ->
                let head1 =
                  let uu____3064 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3064 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3102;
              FStar_Syntax_Syntax.vars = uu____3103;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____3179 = FStar_Syntax_Util.head_and_args top in
           (match uu____3179 with
            | (unary_op,uu____3201) ->
                let head1 =
                  let uu____3225 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____3225 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3269;
              FStar_Syntax_Syntax.vars = uu____3270;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____3308 =
             let uu____3315 =
               let uu____3316 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3316 in
             tc_term uu____3315 e1 in
           (match uu____3308 with
            | (e2,c,g) ->
                let uu____3340 = FStar_Syntax_Util.head_and_args top in
                (match uu____3340 with
                 | (head1,uu____3362) ->
                     let uu____3383 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos in
                     let uu____3410 =
                       let uu____3411 =
                         let uu____3414 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid in
                         FStar_Syntax_Syntax.mk_Total uu____3414 in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____3411 in
                     (uu____3383, uu____3410, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3419;
              FStar_Syntax_Syntax.vars = uu____3420;_},(a1,FStar_Pervasives_Native.None
                                                        )::(a2,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____3473 = FStar_Syntax_Util.head_and_args top in
           (match uu____3473 with
            | (head1,uu____3495) ->
                let env' =
                  let uu____3517 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____3517 in
                let uu____3518 = tc_term env' a1 in
                (match uu____3518 with
                 | (e1,uu____3532,g1) ->
                     let uu____3534 = tc_term env1 a2 in
                     (match uu____3534 with
                      | (e2,t2,g2) ->
                          let g = FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          let uu____3551 =
                            let uu____3554 =
                              let uu____3555 =
                                let uu____3556 =
                                  FStar_Syntax_Syntax.as_arg a1 in
                                let uu____3557 =
                                  let uu____3560 =
                                    FStar_Syntax_Syntax.as_arg a2 in
                                  [uu____3560] in
                                uu____3556 :: uu____3557 in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____3555 in
                            uu____3554 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          (uu____3551, t2, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3565;
              FStar_Syntax_Syntax.vars = uu____3566;_},uu____3567)
           ->
           let uu____3588 =
             let uu____3589 =
               let uu____3594 =
                 let uu____3595 = FStar_Syntax_Print.term_to_string top in
                 FStar_Util.format1 "Ill-applied constant %s" uu____3595 in
               (uu____3594, (e.FStar_Syntax_Syntax.pos)) in
             FStar_Errors.Error uu____3589 in
           FStar_Exn.raise uu____3588
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3602;
              FStar_Syntax_Syntax.vars = uu____3603;_},uu____3604)
           ->
           let uu____3625 =
             let uu____3626 =
               let uu____3631 =
                 let uu____3632 = FStar_Syntax_Print.term_to_string top in
                 FStar_Util.format1 "Ill-applied constant %s" uu____3632 in
               (uu____3631, (e.FStar_Syntax_Syntax.pos)) in
             FStar_Errors.Error uu____3626 in
           FStar_Exn.raise uu____3625
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____3639;
              FStar_Syntax_Syntax.vars = uu____3640;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____3673 =
               let uu____3680 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____3680 with | (env0,uu____3694) -> tc_term env0 e1 in
             match uu____3673 with
             | (e2,c,g) ->
                 let uu____3708 = FStar_Syntax_Util.head_and_args top in
                 (match uu____3708 with
                  | (reify_op,uu____3730) ->
                      let u_c =
                        let uu____3752 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____3752 with
                        | (uu____3759,c',uu____3761) ->
                            let uu____3762 =
                              let uu____3763 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____3763.FStar_Syntax_Syntax.n in
                            (match uu____3762 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____3767 ->
                                 let uu____3768 = FStar_Syntax_Util.type_u () in
                                 (match uu____3768 with
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
                                            let uu____3780 =
                                              let uu____3781 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____3782 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____3783 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____3781 uu____3782
                                                uu____3783 in
                                            failwith uu____3780);
                                       u))) in
                      let repr =
                        let uu____3785 = c.FStar_Syntax_Syntax.comp () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____3785 u_c in
                      let e3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (reify_op, [(e2, aqual)]))
                          FStar_Pervasives_Native.None
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____3806 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____3806
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____3807 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____3807 with
                       | (e4,c2,g') ->
                           let uu____3823 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____3823)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____3825;
              FStar_Syntax_Syntax.vars = uu____3826;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____3868 =
               let uu____3869 =
                 let uu____3870 =
                   let uu____3875 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____3875, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____3870 in
               FStar_Exn.raise uu____3869 in
             let uu____3882 = FStar_Syntax_Util.head_and_args top in
             match uu____3882 with
             | (reflect_op,uu____3904) ->
                 let uu____3925 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____3925 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____3958 =
                        let uu____3959 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____3959 in
                      if uu____3958
                      then no_reflect ()
                      else
                        (let uu____3969 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____3969 with
                         | (env_no_ex,topt) ->
                             let uu____3988 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____4008 =
                                   let uu____4011 =
                                     let uu____4012 =
                                       let uu____4027 =
                                         let uu____4030 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____4031 =
                                           let uu____4034 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____4034] in
                                         uu____4030 :: uu____4031 in
                                       (repr, uu____4027) in
                                     FStar_Syntax_Syntax.Tm_app uu____4012 in
                                   FStar_Syntax_Syntax.mk uu____4011 in
                                 uu____4008 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos in
                               let uu____4040 =
                                 let uu____4047 =
                                   let uu____4048 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____4048
                                     FStar_Pervasives_Native.fst in
                                 tc_tot_or_gtot_term uu____4047 t in
                               match uu____4040 with
                               | (t1,uu____4076,g) ->
                                   let uu____4078 =
                                     let uu____4079 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____4079.FStar_Syntax_Syntax.n in
                                   (match uu____4078 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____4094,(res,uu____4096)::
                                         (wp,uu____4098)::[])
                                        -> (t1, res, wp, g)
                                    | uu____4141 -> failwith "Impossible") in
                             (match uu____3988 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____4172 =
                                    let uu____4177 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____4177 with
                                    | (e2,c,g) ->
                                        ((let uu____4192 =
                                            let uu____4193 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____4193 in
                                          if uu____4192
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____4203 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____4203 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____4211 =
                                                  let uu____4218 =
                                                    let uu____4223 =
                                                      let uu____4224 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____4225 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____4224 uu____4225 in
                                                    (uu____4223,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____4218] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____4211);
                                               (let uu____4234 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____4234)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____4236 =
                                                let uu____4237 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____4237 in
                                              (e2, uu____4236))) in
                                  (match uu____4172 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____4247 =
                                           let uu____4248 =
                                             let uu____4249 =
                                               let uu____4250 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____4250] in
                                             let uu____4251 =
                                               let uu____4260 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____4260] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____4249;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____4251;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____4248 in
                                         FStar_All.pipe_right uu____4247
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____4280 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____4280 with
                                        | (e4,c1,g') ->
                                            let uu____4296 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____4296))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____4343 =
               let uu____4344 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____4344 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____4343 instantiate_both in
           ((let uu____4360 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____4360
             then
               let uu____4361 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____4362 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____4361
                 uu____4362
             else ());
            (let isquote =
               let uu____4365 = FStar_Syntax_Util.head_and_args head1 in
               match uu____4365 with
               | (head2,uu____4381) ->
                   let uu____4402 =
                     let uu____4403 = FStar_Syntax_Util.un_uinst head2 in
                     uu____4403.FStar_Syntax_Syntax.n in
                   (match uu____4402 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.quote_lid
                        -> true
                    | uu____4407 -> false) in
             let uu____4408 = tc_term (no_inst env2) head1 in
             match uu____4408 with
             | (head2,chead,g_head) ->
                 let uu____4424 =
                   let uu____4431 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____4431
                   then
                     let uu____4438 =
                       let uu____4445 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____4445 in
                     match uu____4438 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____4458 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____4460 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c in
                                 Prims.op_Negation uu____4460))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                           if uu____4458
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c in
                         (e1, c1, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2 in
                      let uu____4465 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env3 head2 chead g_head args
                        uu____4465) in
                 (match uu____4424 with
                  | (e1,c,g) ->
                      ((let uu____4478 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____4478
                        then
                          let uu____4479 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____4479
                        else ());
                       (let uu____4481 = comp_check_expected_typ env0 e1 c in
                        match uu____4481 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____4498 =
                                let uu____4499 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____4499.FStar_Syntax_Syntax.n in
                              match uu____4498 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____4503) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___127_4565 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___127_4565.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___127_4565.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___127_4565.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____4614 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____4616 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____4616 in
                            ((let uu____4618 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____4618
                              then
                                let uu____4619 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____4620 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____4619 uu____4620
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____4660 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____4660 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____4680 = tc_term env12 e1 in
                (match uu____4680 with
                 | (e11,c1,g1) ->
                     let uu____4696 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____4706 = FStar_Syntax_Util.type_u () in
                           (match uu____4706 with
                            | (k,uu____4716) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____4718 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____4718, res_t)) in
                     (match uu____4696 with
                      | (env_branches,res_t) ->
                          ((let uu____4728 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____4728
                            then
                              let uu____4729 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____4729
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____4815 =
                              let uu____4820 =
                                FStar_List.fold_right
                                  (fun uu____4866  ->
                                     fun uu____4867  ->
                                       match (uu____4866, uu____4867) with
                                       | ((uu____4930,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____4990 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____4990))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____4820 with
                              | (cases,g) ->
                                  let uu____5029 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____5029, g) in
                            match uu____4815 with
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
                                           (fun uu____5125  ->
                                              match uu____5125 with
                                              | ((pat,wopt,br),uu____5153,lc,uu____5155)
                                                  ->
                                                  let uu____5168 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____5168))) in
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
                                  let uu____5223 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____5223
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____5230 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____5230 in
                                     let lb =
                                       let uu____5234 =
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
                                           uu____5234;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____5238 =
                                         let uu____5241 =
                                           let uu____5242 =
                                             let uu____5255 =
                                               let uu____5256 =
                                                 let uu____5257 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____5257] in
                                               FStar_Syntax_Subst.close
                                                 uu____5256 e_match in
                                             ((false, [lb]), uu____5255) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____5242 in
                                         FStar_Syntax_Syntax.mk uu____5241 in
                                       uu____5238
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____5270 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____5270
                                  then
                                    let uu____5271 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____5272 =
                                      let uu____5273 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____5273 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____5271 uu____5272
                                  else ());
                                 (let uu____5275 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____5275))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5278;
                FStar_Syntax_Syntax.lbunivs = uu____5279;
                FStar_Syntax_Syntax.lbtyp = uu____5280;
                FStar_Syntax_Syntax.lbeff = uu____5281;
                FStar_Syntax_Syntax.lbdef = uu____5282;_}::[]),uu____5283)
           ->
           ((let uu____5303 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5303
             then
               let uu____5304 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____5304
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____5306),uu____5307) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5322;
                FStar_Syntax_Syntax.lbunivs = uu____5323;
                FStar_Syntax_Syntax.lbtyp = uu____5324;
                FStar_Syntax_Syntax.lbeff = uu____5325;
                FStar_Syntax_Syntax.lbdef = uu____5326;_}::uu____5327),uu____5328)
           ->
           ((let uu____5350 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5350
             then
               let uu____5351 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____5351
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____5353),uu____5354) ->
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
        let uu____5380 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5470))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5530))::(uu____5531,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____5532))::
              (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____5605 ->
              FStar_Exn.raise
                (FStar_Errors.Error ("synth_by_tactic: bad application", rng)) in
        match uu____5380 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____5689 = FStar_TypeChecker_Env.expected_typ env in
                  (match uu____5689 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____5695 =
                         let uu____5696 =
                           let uu____5701 =
                             FStar_TypeChecker_Env.get_range env in
                           ("synth_by_tactic: need a type annotation when no expected type is present",
                             uu____5701) in
                         FStar_Errors.Error uu____5696 in
                       FStar_Exn.raise uu____5695) in
            let uu____5704 = FStar_TypeChecker_Env.clear_expected_typ env in
            (match uu____5704 with
             | (env',uu____5718) ->
                 let uu____5723 = tc_term env' typ in
                 (match uu____5723 with
                  | (typ1,uu____5737,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____5740 = tc_tactic env' tau in
                        match uu____5740 with
                        | (tau1,uu____5754,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let t =
                                if env.FStar_TypeChecker_Env.nosynth
                                then
                                  let uu____5762 =
                                    let uu____5763 =
                                      FStar_TypeChecker_Util.fvar_const env
                                        FStar_Parser_Const.magic_lid in
                                    let uu____5764 =
                                      let uu____5765 =
                                        FStar_Syntax_Syntax.as_arg
                                          FStar_Syntax_Util.exp_unit in
                                      [uu____5765] in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____5763
                                      uu____5764 in
                                  uu____5762 FStar_Pervasives_Native.None rng
                                else
                                  (let t =
                                     env.FStar_TypeChecker_Env.synth env'
                                       typ1 tau1 in
                                   (let uu____5771 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Tac") in
                                    if uu____5771
                                    then
                                      let uu____5772 =
                                        FStar_Syntax_Print.term_to_string t in
                                      FStar_Util.print1 "Got %s\n" uu____5772
                                    else ());
                                   t) in
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____5775 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng in
                               tc_term env uu____5775)))))))
and tc_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___128_5779 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___128_5779.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___128_5779.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___128_5779.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___128_5779.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___128_5779.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___128_5779.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___128_5779.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___128_5779.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___128_5779.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___128_5779.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___128_5779.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___128_5779.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___128_5779.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___128_5779.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___128_5779.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___128_5779.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___128_5779.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___128_5779.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___128_5779.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___128_5779.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___128_5779.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___128_5779.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___128_5779.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___128_5779.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___128_5779.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___128_5779.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___128_5779.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___128_5779.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___128_5779.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___128_5779.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___128_5779.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___128_5779.FStar_TypeChecker_Env.dsenv)
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
        let uu___129_5783 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___129_5783.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___129_5783.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___129_5783.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___129_5783.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___129_5783.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___129_5783.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___129_5783.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___129_5783.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___129_5783.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___129_5783.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___129_5783.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___129_5783.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___129_5783.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___129_5783.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___129_5783.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___129_5783.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___129_5783.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___129_5783.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___129_5783.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___129_5783.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___129_5783.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___129_5783.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___129_5783.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___129_5783.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___129_5783.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___129_5783.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___129_5783.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___129_5783.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___129_5783.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___129_5783.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___129_5783.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___129_5783.FStar_TypeChecker_Env.dsenv)
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
          let uu____5799 = tc_tactic env tactic in
          (match uu____5799 with
           | (tactic1,uu____5809,uu____5810) ->
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
        let uu____5849 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____5849 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____5870 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____5870
              then FStar_Util.Inl t1
              else
                (let uu____5876 =
                   let uu____5877 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____5877 in
                 FStar_Util.Inr uu____5876) in
            let is_data_ctor uu___116_5887 =
              match uu___116_5887 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____5890) -> true
              | uu____5897 -> false in
            let uu____5900 =
              (is_data_ctor dc) &&
                (let uu____5902 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____5902) in
            if uu____5900
            then
              let uu____5909 =
                let uu____5910 =
                  let uu____5915 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____5916 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____5915, uu____5916) in
                FStar_Errors.Error uu____5910 in
              FStar_Exn.raise uu____5909
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____5933 =
            let uu____5934 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____5934 in
          failwith uu____5933
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____5968 =
              let uu____5969 = FStar_Syntax_Subst.compress t1 in
              uu____5969.FStar_Syntax_Syntax.n in
            match uu____5968 with
            | FStar_Syntax_Syntax.Tm_arrow uu____5972 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____5985 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___130_6023 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___130_6023.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___130_6023.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___130_6023.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____6075 =
            let uu____6088 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____6088 with
            | FStar_Pervasives_Native.None  ->
                let uu____6103 = FStar_Syntax_Util.type_u () in
                (match uu____6103 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____6075 with
           | (t,uu____6140,g0) ->
               let uu____6154 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____6154 with
                | (e1,uu____6174,g1) ->
                    let uu____6188 =
                      let uu____6189 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____6189
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____6190 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____6188, uu____6190)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____6192 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____6205 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____6205)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____6192 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___131_6224 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___131_6224.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___131_6224.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____6227 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____6227 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____6248 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____6248
                       then FStar_Util.Inl t1
                       else
                         (let uu____6254 =
                            let uu____6255 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____6255 in
                          FStar_Util.Inr uu____6254) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6261;
             FStar_Syntax_Syntax.vars = uu____6262;_},uu____6263)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____6268 =
            let uu____6269 =
              let uu____6274 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____6274) in
            FStar_Errors.Error uu____6269 in
          FStar_Exn.raise uu____6268
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____6282 =
            let uu____6283 =
              let uu____6288 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____6288) in
            FStar_Errors.Error uu____6283 in
          FStar_Exn.raise uu____6282
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6296;
             FStar_Syntax_Syntax.vars = uu____6297;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____6306 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6306 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____6329 =
                     let uu____6330 =
                       let uu____6335 =
                         let uu____6336 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____6337 =
                           FStar_Util.string_of_int (FStar_List.length us1) in
                         let uu____6338 =
                           FStar_Util.string_of_int (FStar_List.length us') in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____6336 uu____6337 uu____6338 in
                       let uu____6339 = FStar_TypeChecker_Env.get_range env1 in
                       (uu____6335, uu____6339) in
                     FStar_Errors.Error uu____6330 in
                   FStar_Exn.raise uu____6329)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____6355 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6359 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6359 us1 in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6361 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6361 with
           | ((us,t),range) ->
               ((let uu____6384 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____6384
                 then
                   let uu____6385 =
                     let uu____6386 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____6386 in
                   let uu____6387 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____6388 = FStar_Range.string_of_range range in
                   let uu____6389 = FStar_Range.string_of_use_range range in
                   let uu____6390 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____6385 uu____6387 uu____6388 uu____6389 uu____6390
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6395 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6395 us in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant top.FStar_Syntax_Syntax.pos c in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6419 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6419 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____6433 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____6433 with
                | (env2,uu____6447) ->
                    let uu____6452 = tc_binders env2 bs1 in
                    (match uu____6452 with
                     | (bs2,env3,g,us) ->
                         let uu____6471 = tc_comp env3 c1 in
                         (match uu____6471 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___132_6490 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___132_6490.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___132_6490.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____6499 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____6499 in
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
          let uu____6518 =
            let uu____6523 =
              let uu____6524 = FStar_Syntax_Syntax.mk_binder x in
              [uu____6524] in
            FStar_Syntax_Subst.open_term uu____6523 phi in
          (match uu____6518 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____6534 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____6534 with
                | (env2,uu____6548) ->
                    let uu____6553 =
                      let uu____6566 = FStar_List.hd x1 in
                      tc_binder env2 uu____6566 in
                    (match uu____6553 with
                     | (x2,env3,f1,u) ->
                         ((let uu____6594 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____6594
                           then
                             let uu____6595 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____6596 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____6597 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____6595 uu____6596 uu____6597
                           else ());
                          (let uu____6599 = FStar_Syntax_Util.type_u () in
                           match uu____6599 with
                           | (t_phi,uu____6611) ->
                               let uu____6612 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____6612 with
                                | (phi2,uu____6626,f2) ->
                                    let e1 =
                                      let uu___133_6631 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___133_6631.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___133_6631.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____6638 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____6638 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____6651) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____6674 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____6674
            then
              let uu____6675 =
                FStar_Syntax_Print.term_to_string
                  (let uu___134_6678 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___134_6678.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___134_6678.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____6675
            else ());
           (let uu____6684 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____6684 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____6697 ->
          let uu____6698 =
            let uu____6699 = FStar_Syntax_Print.term_to_string top in
            let uu____6700 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____6699
              uu____6700 in
          failwith uu____6698
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
      | FStar_Const.Const_bool uu____6709 -> FStar_Syntax_Util.t_bool
      | FStar_Const.Const_int (uu____6710,FStar_Pervasives_Native.None ) ->
          FStar_Syntax_Syntax.t_int
      | FStar_Const.Const_int
          (uu____6721,FStar_Pervasives_Native.Some uu____6722) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____6737 -> FStar_Syntax_Syntax.t_string
      | FStar_Const.Const_float uu____6742 -> FStar_Syntax_Syntax.t_float
      | FStar_Const.Const_char uu____6743 -> FStar_Syntax_Syntax.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____6744 -> FStar_Syntax_Syntax.t_range
      | FStar_Const.Const_range_of  ->
          let uu____6745 =
            let uu____6746 =
              let uu____6751 =
                let uu____6752 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6752 in
              (uu____6751, r) in
            FStar_Errors.Error uu____6746 in
          FStar_Exn.raise uu____6745
      | FStar_Const.Const_set_range_of  ->
          let uu____6753 =
            let uu____6754 =
              let uu____6759 =
                let uu____6760 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6760 in
              (uu____6759, r) in
            FStar_Errors.Error uu____6754 in
          FStar_Exn.raise uu____6753
      | FStar_Const.Const_reify  ->
          let uu____6761 =
            let uu____6762 =
              let uu____6767 =
                let uu____6768 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6768 in
              (uu____6767, r) in
            FStar_Errors.Error uu____6762 in
          FStar_Exn.raise uu____6761
      | FStar_Const.Const_reflect uu____6769 ->
          let uu____6770 =
            let uu____6771 =
              let uu____6776 =
                let uu____6777 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6777 in
              (uu____6776, r) in
            FStar_Errors.Error uu____6771 in
          FStar_Exn.raise uu____6770
      | uu____6778 ->
          FStar_Exn.raise (FStar_Errors.Error ("Unsupported constant", r))
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
      | FStar_Syntax_Syntax.Total (t,uu____6795) ->
          let uu____6804 = FStar_Syntax_Util.type_u () in
          (match uu____6804 with
           | (k,u) ->
               let uu____6817 = tc_check_tot_or_gtot_term env t k in
               (match uu____6817 with
                | (t1,uu____6831,g) ->
                    let uu____6833 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____6833, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____6835) ->
          let uu____6844 = FStar_Syntax_Util.type_u () in
          (match uu____6844 with
           | (k,u) ->
               let uu____6857 = tc_check_tot_or_gtot_term env t k in
               (match uu____6857 with
                | (t1,uu____6871,g) ->
                    let uu____6873 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____6873, u, g)))
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
            let uu____6881 =
              let uu____6882 =
                let uu____6883 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____6883 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____6882 in
            uu____6881 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____6886 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____6886 with
           | (tc1,uu____6900,f) ->
               let uu____6902 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____6902 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____6946 =
                        let uu____6947 = FStar_Syntax_Subst.compress head3 in
                        uu____6947.FStar_Syntax_Syntax.n in
                      match uu____6946 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____6950,us) -> us
                      | uu____6956 -> [] in
                    let uu____6957 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____6957 with
                     | (uu____6978,args1) ->
                         let uu____7000 =
                           let uu____7019 = FStar_List.hd args1 in
                           let uu____7032 = FStar_List.tl args1 in
                           (uu____7019, uu____7032) in
                         (match uu____7000 with
                          | (res,args2) ->
                              let uu____7097 =
                                let uu____7106 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___117_7134  ->
                                          match uu___117_7134 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____7142 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____7142 with
                                               | (env1,uu____7154) ->
                                                   let uu____7159 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____7159 with
                                                    | (e1,uu____7171,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____7106
                                  FStar_List.unzip in
                              (match uu____7097 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___135_7210 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___135_7210.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___135_7210.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____7214 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____7214 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____7218 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____7218))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____7226 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____7227 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____7237 = aux u3 in FStar_Syntax_Syntax.U_succ uu____7237
        | FStar_Syntax_Syntax.U_max us ->
            let uu____7241 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____7241
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____7246 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____7246 FStar_Pervasives_Native.snd
         | uu____7255 -> aux u)
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
            let uu____7279 =
              let uu____7280 =
                let uu____7285 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____7285, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____7280 in
            FStar_Exn.raise uu____7279 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____7375 bs2 bs_expected1 =
              match uu____7375 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____7543)) ->
                             let uu____7548 =
                               let uu____7549 =
                                 let uu____7554 =
                                   let uu____7555 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____7555 in
                                 let uu____7556 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____7554, uu____7556) in
                               FStar_Errors.Error uu____7549 in
                             FStar_Exn.raise uu____7548
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____7557),FStar_Pervasives_Native.None ) ->
                             let uu____7562 =
                               let uu____7563 =
                                 let uu____7568 =
                                   let uu____7569 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____7569 in
                                 let uu____7570 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____7568, uu____7570) in
                               FStar_Errors.Error uu____7563 in
                             FStar_Exn.raise uu____7562
                         | uu____7571 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____7577 =
                           let uu____7582 =
                             let uu____7583 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____7583.FStar_Syntax_Syntax.n in
                           match uu____7582 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____7590 ->
                               ((let uu____7592 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____7592
                                 then
                                   let uu____7593 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____7593
                                 else ());
                                (let uu____7595 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____7595 with
                                 | (t,uu____7607,g1) ->
                                     let g2 =
                                       let uu____7610 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____7611 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____7610
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____7611 in
                                     let g3 =
                                       let uu____7613 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____7613 in
                                     (t, g3))) in
                         match uu____7577 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___136_7641 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___136_7641.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___136_7641.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____7654 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____7654 in
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
                  | uu____7800 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____7807 = tc_binders env1 bs in
                  match uu____7807 with
                  | (bs1,envbody,g,uu____7837) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____7881 =
                    let uu____7882 = FStar_Syntax_Subst.compress t2 in
                    uu____7882.FStar_Syntax_Syntax.n in
                  match uu____7881 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____7905 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____7927 -> failwith "Impossible");
                       (let uu____7934 = tc_binders env1 bs in
                        match uu____7934 with
                        | (bs1,envbody,g,uu____7966) ->
                            let uu____7967 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____7967 with
                             | (envbody1,uu____7995) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____8006;
                         FStar_Syntax_Syntax.pos = uu____8007;
                         FStar_Syntax_Syntax.vars = uu____8008;_},uu____8009)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8051 -> failwith "Impossible");
                       (let uu____8058 = tc_binders env1 bs in
                        match uu____8058 with
                        | (bs1,envbody,g,uu____8090) ->
                            let uu____8091 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____8091 with
                             | (envbody1,uu____8119) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____8131) ->
                      let uu____8136 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____8136 with
                       | (uu____8177,bs1,bs',copt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____8220 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____8220 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____8320 c_expected2 =
                               match uu____8320 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____8435 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____8435)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____8466 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____8466 in
                                        let uu____8467 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____8467)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        let uu____8492 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c) in
                                        if uu____8492
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
                                               let uu____8540 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____8540 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____8561 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____8561 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____8609 =
                                                           let uu____8640 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____8640,
                                                             subst2) in
                                                         handle_more
                                                           uu____8609
                                                           c_expected4))
                                           | uu____8657 ->
                                               let uu____8658 =
                                                 let uu____8659 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____8659 in
                                               fail uu____8658 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____8689 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____8689 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___137_8748 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___137_8748.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___137_8748.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___137_8748.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___137_8748.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___137_8748.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___137_8748.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___137_8748.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___137_8748.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___137_8748.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___137_8748.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___137_8748.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___137_8748.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___137_8748.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___137_8748.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___137_8748.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___137_8748.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___137_8748.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___137_8748.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___137_8748.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___137_8748.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___137_8748.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___137_8748.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___137_8748.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___137_8748.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___137_8748.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___137_8748.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___137_8748.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___137_8748.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___137_8748.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___137_8748.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___137_8748.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___137_8748.FStar_TypeChecker_Env.dsenv)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____8787  ->
                                     fun uu____8788  ->
                                       match (uu____8787, uu____8788) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____8833 =
                                             let uu____8840 =
                                               let uu____8841 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____8841
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____8840 t3 in
                                           (match uu____8833 with
                                            | (t4,uu____8863,uu____8864) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____8874 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___138_8877
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___138_8877.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___138_8877.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____8874 ::
                                                        letrec_binders
                                                  | uu____8878 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____8883 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____8883 with
                            | (envbody,bs1,g,c) ->
                                let uu____8934 =
                                  let uu____8941 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____8941
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____8934 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body1, g))))
                  | uu____8990 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____9011 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____9011
                      else
                        (let uu____9013 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1 in
                         match uu____9013 with
                         | (uu____9052,bs1,uu____9054,c_opt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____9074 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____9074 with
          | (env1,topt) ->
              ((let uu____9094 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____9094
                then
                  let uu____9095 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____9095
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____9099 = expected_function_typ1 env1 topt body in
                match uu____9099 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let uu____9139 =
                      let should_check_expected_effect =
                        let uu____9147 =
                          let uu____9154 =
                            let uu____9155 =
                              FStar_Syntax_Subst.compress body1 in
                            uu____9155.FStar_Syntax_Syntax.n in
                          (c_opt, uu____9154) in
                        match uu____9147 with
                        | (FStar_Pervasives_Native.None
                           ,FStar_Syntax_Syntax.Tm_ascribed
                           (uu____9160,(FStar_Util.Inr expected_c,uu____9162),uu____9163))
                            -> false
                        | uu____9212 -> true in
                      let uu____9219 =
                        tc_term
                          (let uu___139_9228 = envbody in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___139_9228.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___139_9228.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___139_9228.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___139_9228.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___139_9228.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___139_9228.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___139_9228.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___139_9228.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___139_9228.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___139_9228.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___139_9228.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___139_9228.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___139_9228.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = false;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___139_9228.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq = use_eq;
                             FStar_TypeChecker_Env.is_iface =
                               (uu___139_9228.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___139_9228.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___139_9228.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___139_9228.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___139_9228.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___139_9228.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___139_9228.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___139_9228.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___139_9228.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___139_9228.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qname_and_index =
                               (uu___139_9228.FStar_TypeChecker_Env.qname_and_index);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___139_9228.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth =
                               (uu___139_9228.FStar_TypeChecker_Env.synth);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___139_9228.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___139_9228.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___139_9228.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___139_9228.FStar_TypeChecker_Env.dsenv)
                           }) body1 in
                      match uu____9219 with
                      | (body2,cbody,guard_body) ->
                          let guard_body1 =
                            FStar_TypeChecker_Rel.solve_deferred_constraints
                              envbody guard_body in
                          if should_check_expected_effect
                          then
                            let uu____9245 =
                              let uu____9252 =
                                let uu____9257 =
                                  cbody.FStar_Syntax_Syntax.comp () in
                                (body2, uu____9257) in
                              check_expected_effect
                                (let uu___140_9264 = envbody in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___140_9264.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___140_9264.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___140_9264.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___140_9264.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___140_9264.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___140_9264.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___140_9264.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___140_9264.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___140_9264.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___140_9264.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___140_9264.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___140_9264.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___140_9264.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___140_9264.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___140_9264.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___140_9264.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___140_9264.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___140_9264.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___140_9264.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___140_9264.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___140_9264.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___140_9264.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___140_9264.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___140_9264.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___140_9264.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___140_9264.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___140_9264.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___140_9264.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___140_9264.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___140_9264.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___140_9264.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___140_9264.FStar_TypeChecker_Env.dsenv)
                                 }) c_opt uu____9252 in
                            (match uu____9245 with
                             | (body3,cbody1,guard) ->
                                 let uu____9274 =
                                   FStar_TypeChecker_Rel.conj_guard
                                     guard_body1 guard in
                                 (body3, cbody1, uu____9274))
                          else
                            (let uu____9276 =
                               cbody.FStar_Syntax_Syntax.comp () in
                             (body2, uu____9276, guard_body1)) in
                    (match uu____9139 with
                     | (body2,cbody,guard) ->
                         let guard1 =
                           let uu____9291 =
                             env1.FStar_TypeChecker_Env.top_level ||
                               (let uu____9293 =
                                  FStar_TypeChecker_Env.should_verify env1 in
                                Prims.op_Negation uu____9293) in
                           if uu____9291
                           then
                             let uu____9294 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             FStar_TypeChecker_Rel.discharge_guard envbody
                               uu____9294
                           else
                             (let guard1 =
                                let uu____9297 =
                                  FStar_TypeChecker_Rel.conj_guard g guard in
                                FStar_TypeChecker_Rel.close_guard env1
                                  (FStar_List.append bs1 letrec_binders)
                                  uu____9297 in
                              guard1) in
                         let tfun_computed =
                           FStar_Syntax_Util.arrow bs1 cbody in
                         let e =
                           FStar_Syntax_Util.abs bs1 body2
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp
                                   (FStar_Util.dflt cbody c_opt))) in
                         let uu____9306 =
                           match tfun_opt with
                           | FStar_Pervasives_Native.Some t ->
                               let t1 = FStar_Syntax_Subst.compress t in
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_arrow uu____9327 ->
                                    (e, t1, guard1)
                                | uu____9340 ->
                                    let uu____9341 =
                                      FStar_TypeChecker_Util.check_and_ascribe
                                        env1 e tfun_computed t1 in
                                    (match uu____9341 with
                                     | (e1,guard') ->
                                         let uu____9354 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 guard' in
                                         (e1, t1, uu____9354)))
                           | FStar_Pervasives_Native.None  ->
                               (e, tfun_computed, guard1) in
                         (match uu____9306 with
                          | (e1,tfun,guard2) ->
                              let c =
                                if env1.FStar_TypeChecker_Env.top_level
                                then FStar_Syntax_Syntax.mk_Total tfun
                                else
                                  FStar_TypeChecker_Util.return_value env1
                                    tfun e1 in
                              let uu____9368 =
                                FStar_TypeChecker_Util.strengthen_precondition
                                  FStar_Pervasives_Native.None env1 e1
                                  (FStar_Syntax_Util.lcomp_of_comp c) guard2 in
                              (match uu____9368 with
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
              (let uu____9417 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____9417
               then
                 let uu____9418 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____9419 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____9418
                   uu____9419
               else ());
              (let monadic_application uu____9476 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____9476 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___141_9535 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___141_9535.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___141_9535.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___141_9535.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____9536 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
                       | uu____9551 ->
                           let g =
                             let uu____9559 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____9559
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____9560 =
                             let uu____9561 =
                               let uu____9564 =
                                 let uu____9565 =
                                   let uu____9566 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____9566 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____9565 in
                               FStar_Syntax_Syntax.mk_Total uu____9564 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____9561 in
                           (uu____9560, g) in
                     (match uu____9536 with
                      | (cres2,guard1) ->
                          ((let uu____9580 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____9580
                            then
                              let uu____9581 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____9581
                            else ());
                           (let cres3 =
                              let uu____9584 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____9584
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
                                   fun uu____9618  ->
                                     match uu____9618 with
                                     | ((e,q),x,c) ->
                                         let uu____9651 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____9651
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
                              let uu____9663 =
                                let uu____9664 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____9664.FStar_Syntax_Syntax.n in
                              match uu____9663 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____9668 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____9689  ->
                                         match uu____9689 with
                                         | (arg,uu____9703,uu____9704) -> arg
                                             :: args1) [] arg_comps_rev in
                                let app =
                                  FStar_Syntax_Syntax.mk_Tm_app head2 args1
                                    FStar_Pervasives_Native.None r in
                                let app1 =
                                  FStar_TypeChecker_Util.maybe_lift env app
                                    cres3.FStar_Syntax_Syntax.eff_name
                                    comp1.FStar_Syntax_Syntax.eff_name
                                    comp1.FStar_Syntax_Syntax.res_typ in
                                FStar_TypeChecker_Util.maybe_monadic env app1
                                  comp1.FStar_Syntax_Syntax.eff_name
                                  comp1.FStar_Syntax_Syntax.res_typ
                              else
                                (let uu____9714 =
                                   let map_fun uu____9776 =
                                     match uu____9776 with
                                     | ((e,q),uu____9811,c) ->
                                         let uu____9821 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____9821
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
                                            let uu____9871 =
                                              let uu____9876 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____9876, q) in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____9871)) in
                                   let uu____9905 =
                                     let uu____9930 =
                                       let uu____9953 =
                                         let uu____9968 =
                                           let uu____9977 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____9977,
                                             FStar_Pervasives_Native.None,
                                             chead1) in
                                         uu____9968 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____9953 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____9930 in
                                   match uu____9905 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____10150 =
                                         let uu____10151 =
                                           FStar_List.hd reverse_args in
                                         FStar_Pervasives_Native.fst
                                           uu____10151 in
                                       let uu____10160 =
                                         let uu____10167 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____10167 in
                                       (lifted_args, uu____10150,
                                         uu____10160) in
                                 match uu____9714 with
                                 | (lifted_args,head3,args1) ->
                                     let app =
                                       FStar_Syntax_Syntax.mk_Tm_app head3
                                         args1 FStar_Pervasives_Native.None r in
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
                                     let bind_lifted_args e uu___118_10270 =
                                       match uu___118_10270 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____10325 =
                                               let uu____10328 =
                                                 let uu____10329 =
                                                   let uu____10342 =
                                                     let uu____10343 =
                                                       let uu____10344 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____10344] in
                                                     FStar_Syntax_Subst.close
                                                       uu____10343 e in
                                                   ((false, [lb]),
                                                     uu____10342) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____10329 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10328 in
                                             uu____10325
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
                            let uu____10374 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp1
                                guard1 in
                            match uu____10374 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____10465 bs args1 =
                 match uu____10465 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____10612))::rest,
                         (uu____10614,FStar_Pervasives_Native.None )::uu____10615)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t in
                          let uu____10676 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____10676 with
                           | (varg,uu____10696,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____10718 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____10718) in
                               let uu____10719 =
                                 let uu____10754 =
                                   let uu____10769 =
                                     let uu____10782 =
                                       let uu____10783 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____10783
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____10782) in
                                   uu____10769 :: outargs in
                                 let uu____10802 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____10754, (arg :: arg_rets),
                                   uu____10802, fvs) in
                               tc_args head_info uu____10719 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____10904),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____10905)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____10918 ->
                                FStar_Exn.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___142_10929 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___142_10929.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___142_10929.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____10931 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____10931
                             then
                               let uu____10932 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____10932
                             else ());
                            (let targ1 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___143_10937 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___143_10937.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___143_10937.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___143_10937.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___143_10937.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___143_10937.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___143_10937.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___143_10937.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___143_10937.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___143_10937.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___143_10937.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___143_10937.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___143_10937.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___143_10937.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___143_10937.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___143_10937.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___143_10937.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___143_10937.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___143_10937.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___143_10937.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___143_10937.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___143_10937.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___143_10937.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___143_10937.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___143_10937.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___143_10937.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___143_10937.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___143_10937.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___143_10937.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___143_10937.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___143_10937.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___143_10937.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___143_10937.FStar_TypeChecker_Env.dsenv)
                               } in
                             (let uu____10939 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____10939
                              then
                                let uu____10940 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____10941 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____10942 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____10940 uu____10941 uu____10942
                              else ());
                             (let uu____10944 = tc_term env2 e in
                              match uu____10944 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____10971 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____10971 in
                                  let uu____10972 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____10972
                                  then
                                    let subst2 =
                                      let uu____10980 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____10980
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
                      | (uu____11074,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____11110) ->
                          let uu____11161 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____11161 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____11195 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____11195
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____11220 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____11220 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____11243 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____11243
                                            then
                                              FStar_Errors.warn
                                                tres1.FStar_Syntax_Syntax.pos
                                                "Potentially redundant explicit currying of a function type"
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____11285 when Prims.op_Negation norm1
                                     ->
                                     let uu____11286 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____11286
                                 | uu____11287 ->
                                     let uu____11288 =
                                       let uu____11289 =
                                         let uu____11294 =
                                           let uu____11295 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____11296 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____11295 uu____11296 in
                                         let uu____11303 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____11294, uu____11303) in
                                       FStar_Errors.Error uu____11289 in
                                     FStar_Exn.raise uu____11288 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____11322 =
                   let uu____11323 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____11323.FStar_Syntax_Syntax.n in
                 match uu____11322 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____11334 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____11435 = tc_term env1 e in
                           (match uu____11435 with
                            | (e1,c,g_e) ->
                                let uu____11457 = tc_args1 env1 tl1 in
                                (match uu____11457 with
                                 | (args2,comps,g_rest) ->
                                     let uu____11497 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____11497))) in
                     let uu____11518 = tc_args1 env args in
                     (match uu____11518 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____11555 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____11593  ->
                                      match uu____11593 with
                                      | (uu____11606,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____11555 in
                          let ml_or_tot t r1 =
                            let uu____11623 = FStar_Options.ml_ish () in
                            if uu____11623
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____11626 =
                              let uu____11629 =
                                let uu____11630 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____11630
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____11629 in
                            ml_or_tot uu____11626 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____11643 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____11643
                            then
                              let uu____11644 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____11645 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____11646 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____11644 uu____11645 uu____11646
                            else ());
                           (let uu____11649 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____11649);
                           (let comp =
                              let uu____11651 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____11662  ->
                                   fun out  ->
                                     match uu____11662 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____11651 in
                            let uu____11676 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____11679 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____11676, comp, uu____11679))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____11682;
                        FStar_Syntax_Syntax.pos = uu____11683;
                        FStar_Syntax_Syntax.vars = uu____11684;_},uu____11685)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____11806 = tc_term env1 e in
                           (match uu____11806 with
                            | (e1,c,g_e) ->
                                let uu____11828 = tc_args1 env1 tl1 in
                                (match uu____11828 with
                                 | (args2,comps,g_rest) ->
                                     let uu____11868 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____11868))) in
                     let uu____11889 = tc_args1 env args in
                     (match uu____11889 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____11926 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____11964  ->
                                      match uu____11964 with
                                      | (uu____11977,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____11926 in
                          let ml_or_tot t r1 =
                            let uu____11994 = FStar_Options.ml_ish () in
                            if uu____11994
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____11997 =
                              let uu____12000 =
                                let uu____12001 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____12001
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____12000 in
                            ml_or_tot uu____11997 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____12014 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____12014
                            then
                              let uu____12015 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____12016 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____12017 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____12015 uu____12016 uu____12017
                            else ());
                           (let uu____12020 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____12020);
                           (let comp =
                              let uu____12022 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____12033  ->
                                   fun out  ->
                                     match uu____12033 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____12022 in
                            let uu____12047 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____12050 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____12047, comp, uu____12050))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____12071 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____12071 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____12136) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____12142,uu____12143) -> check_function_app t
                 | uu____12184 ->
                     let uu____12185 =
                       let uu____12186 =
                         let uu____12191 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____12191, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____12186 in
                     FStar_Exn.raise uu____12185 in
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
                  let uu____12261 =
                    FStar_List.fold_left2
                      (fun uu____12304  ->
                         fun uu____12305  ->
                           fun uu____12306  ->
                             match (uu____12304, uu____12305, uu____12306)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Exn.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____12374 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____12374 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____12392 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____12392 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____12396 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____12396)
                                              &&
                                              (let uu____12398 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____12398)) in
                                       let uu____12399 =
                                         let uu____12408 =
                                           let uu____12417 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____12417] in
                                         FStar_List.append seen uu____12408 in
                                       let uu____12424 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____12399, uu____12424, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____12261 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r in
                       let c1 =
                         if ghost
                         then
                           let uu____12460 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____12460
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____12462 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____12462 with | (c2,g) -> (e, c2, g)))
              | uu____12479 ->
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
           FStar_Pervasives_Native.tuple3,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,
          FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple4
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____12513 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____12513 with
        | (pattern,when_clause,branch_exp) ->
            let uu____12549 = branch1 in
            (match uu____12549 with
             | (cpat,uu____12581,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let tc_annot env1 t =
                     let uu____12640 = FStar_Syntax_Util.type_u () in
                     match uu____12640 with
                     | (tu,u) ->
                         let uu____12647 =
                           tc_check_tot_or_gtot_term env1 t tu in
                         (match uu____12647 with
                          | (t1,uu____12655,g) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env1
                                 g;
                               t1)) in
                   let uu____12658 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0
                       tc_annot in
                   match uu____12658 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____12687 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____12687
                         then
                           let uu____12688 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____12689 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____12688 uu____12689
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____12692 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____12692 with
                         | (env1,uu____12712) ->
                             let env11 =
                               let uu___144_12718 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___144_12718.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___144_12718.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___144_12718.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___144_12718.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___144_12718.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___144_12718.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___144_12718.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___144_12718.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___144_12718.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___144_12718.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___144_12718.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___144_12718.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___144_12718.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___144_12718.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___144_12718.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___144_12718.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___144_12718.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___144_12718.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___144_12718.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___144_12718.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___144_12718.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___144_12718.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___144_12718.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___144_12718.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___144_12718.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___144_12718.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___144_12718.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___144_12718.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___144_12718.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___144_12718.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___144_12718.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___144_12718.FStar_TypeChecker_Env.dsenv)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____12721 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____12721
                               then
                                 let uu____12722 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____12723 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____12722 uu____12723
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t in
                               let uu____12726 =
                                 tc_tot_or_gtot_term env12 exp in
                               match uu____12726 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___145_12749 = g in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___145_12749.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___145_12749.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___145_12749.FStar_TypeChecker_Env.implicits)
                                     } in
                                   let uu____12750 =
                                     let uu____12751 =
                                       FStar_TypeChecker_Rel.teq_nosmt env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t in
                                     if uu____12751
                                     then
                                       let env13 =
                                         FStar_TypeChecker_Env.set_range
                                           env12 exp1.FStar_Syntax_Syntax.pos in
                                       let uu____12753 =
                                         FStar_TypeChecker_Rel.discharge_guard_no_smt
                                           env13 g1 in
                                       FStar_All.pipe_right uu____12753
                                         FStar_TypeChecker_Rel.resolve_implicits
                                     else
                                       (let uu____12755 =
                                          let uu____12756 =
                                            let uu____12761 =
                                              let uu____12762 =
                                                FStar_Syntax_Print.term_to_string
                                                  lc.FStar_Syntax_Syntax.res_typ in
                                              let uu____12763 =
                                                FStar_Syntax_Print.term_to_string
                                                  expected_pat_t in
                                              FStar_Util.format2
                                                "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                                uu____12762 uu____12763 in
                                            (uu____12761,
                                              (exp1.FStar_Syntax_Syntax.pos)) in
                                          FStar_Errors.Error uu____12756 in
                                        FStar_Exn.raise uu____12755) in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1 in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____12780 =
                                       let uu____12781 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____12781 in
                                     if uu____12780
                                     then
                                       let unresolved =
                                         let uu____12793 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____12793
                                           FStar_Util.set_elements in
                                       let uu____12820 =
                                         let uu____12821 =
                                           let uu____12826 =
                                             let uu____12827 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____12828 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____12829 =
                                               let uu____12830 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____12848  ->
                                                         match uu____12848
                                                         with
                                                         | (u,uu____12854) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____12830
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____12827 uu____12828
                                               uu____12829 in
                                           (uu____12826,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____12821 in
                                       FStar_Exn.raise uu____12820
                                     else ());
                                    (let uu____12859 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____12859
                                     then
                                       let uu____12860 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____12860
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____12869 =
                   let uu____12876 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____12876
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____12869 with
                  | (scrutinee_env,uu____12900) ->
                      let uu____12905 = tc_pat true pat_t pattern in
                      (match uu____12905 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____12943 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____12965 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____12965
                                 then
                                   FStar_Exn.raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____12979 =
                                      let uu____12986 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool in
                                      tc_term uu____12986 e in
                                    match uu____12979 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g)) in
                           (match uu____12943 with
                            | (when_clause1,g_when) ->
                                let uu____13020 = tc_term pat_env branch_exp in
                                (match uu____13020 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some w ->
                                           let uu____13052 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_41  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_41) uu____13052 in
                                     let uu____13055 =
                                       let eqs =
                                         let uu____13065 =
                                           let uu____13066 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____13066 in
                                         if uu____13065
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____13073 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____13090 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____13091 ->
                                                FStar_Pervasives_Native.None
                                            | uu____13092 ->
                                                let uu____13093 =
                                                  let uu____13094 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____13094 pat_t
                                                    scrutinee_tm e in
                                                FStar_Pervasives_Native.Some
                                                  uu____13093) in
                                       let uu____13095 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch in
                                       match uu____13095 with
                                       | (c1,g_branch1) ->
                                           let uu____13110 =
                                             match (eqs, when_condition) with
                                             | uu____13123 when
                                                 let uu____13132 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation
                                                   uu____13132
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
                                                 let uu____13144 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____13145 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____13144, uu____13145)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____13154 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____13154 in
                                                 let uu____13155 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____13156 =
                                                   let uu____13157 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____13157 g_when in
                                                 (uu____13155, uu____13156)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____13165 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____13165, g_when) in
                                           (match uu____13110 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____13177 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____13178 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____13177, uu____13178,
                                                  g_branch1)) in
                                     (match uu____13055 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____13199 =
                                              let uu____13200 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____13200 in
                                            if uu____13199
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____13230 =
                                                     let uu____13231 =
                                                       let uu____13232 =
                                                         let uu____13235 =
                                                           let uu____13242 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____13242 in
                                                         FStar_Pervasives_Native.snd
                                                           uu____13235 in
                                                       FStar_List.length
                                                         uu____13232 in
                                                     uu____13231 >
                                                       (Prims.parse_int "1") in
                                                   if uu____13230
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____13248 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____13248 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____13269 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None in
                                                         let disc1 =
                                                           let uu____13284 =
                                                             let uu____13285
                                                               =
                                                               let uu____13286
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____13286] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____13285 in
                                                           uu____13284
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____13289 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool in
                                                         [uu____13289]
                                                   else [] in
                                                 let fail uu____13294 =
                                                   let uu____13295 =
                                                     let uu____13296 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____13297 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____13298 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____13296
                                                       uu____13297
                                                       uu____13298 in
                                                   failwith uu____13295 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____13309) ->
                                                       head_constructor t1
                                                   | uu____13314 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____13316 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____13316
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____13319 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____13336;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____13337;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____13338;_},uu____13339)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____13376 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____13378 =
                                                       let uu____13379 =
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____13379
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____13378]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____13380 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____13388 =
                                                       let uu____13389 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____13389 in
                                                     if uu____13388
                                                     then []
                                                     else
                                                       (let uu____13393 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13393)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____13396 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____13398 =
                                                       let uu____13399 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____13399 in
                                                     if uu____13398
                                                     then []
                                                     else
                                                       (let uu____13403 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13403)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____13429 =
                                                       let uu____13430 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____13430 in
                                                     if uu____13429
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____13437 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____13469
                                                                     ->
                                                                    match uu____13469
                                                                    with
                                                                    | 
                                                                    (ei,uu____13479)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____13485
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____13485
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____13506
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____13520
                                                                    =
                                                                    let uu____13521
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____13522
                                                                    =
                                                                    let uu____13523
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____13523] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____13521
                                                                    uu____13522 in
                                                                    uu____13520
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____13437
                                                            FStar_List.flatten in
                                                        let uu____13532 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____13532
                                                          sub_term_guards)
                                                 | uu____13535 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____13547 =
                                                   let uu____13548 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____13548 in
                                                 if uu____13547
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____13551 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____13551 in
                                                    let uu____13556 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____13556 with
                                                    | (k,uu____13562) ->
                                                        let uu____13563 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____13563
                                                         with
                                                         | (t1,uu____13571,uu____13572)
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
                                          ((let uu____13578 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____13578
                                            then
                                              let uu____13579 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____13579
                                            else ());
                                           (let uu____13581 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____13581, branch_guard, c1,
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
          let uu____13607 = check_let_bound_def true env1 lb in
          (match uu____13607 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____13629 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____13646 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____13646, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____13649 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____13649
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____13653 =
                      let uu____13666 =
                        let uu____13681 =
                          let uu____13690 =
                            let uu____13703 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____13703) in
                          [uu____13690] in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____13681 in
                      FStar_List.hd uu____13666 in
                    match uu____13653 with
                    | (uu____13756,univs1,e11,c11,gvs) ->
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
                        (g13, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____13629 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____13779 =
                      let uu____13786 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____13786
                      then
                        let uu____13793 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____13793 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____13816 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____13816
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____13817 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____13817, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____13827 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____13827
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm] env1) in
                          let e21 =
                            let uu____13835 =
                              FStar_Syntax_Util.is_pure_comp c in
                            if uu____13835
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
                    (match uu____13779 with
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
                         let uu____13859 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         (uu____13859,
                           (FStar_Syntax_Util.lcomp_of_comp cres),
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____13874 -> failwith "Impossible"
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
            let uu___146_13905 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___146_13905.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___146_13905.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___146_13905.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___146_13905.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___146_13905.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___146_13905.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___146_13905.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___146_13905.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___146_13905.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___146_13905.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___146_13905.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___146_13905.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___146_13905.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___146_13905.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___146_13905.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___146_13905.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___146_13905.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___146_13905.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___146_13905.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___146_13905.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___146_13905.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___146_13905.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___146_13905.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___146_13905.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___146_13905.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___146_13905.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___146_13905.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___146_13905.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___146_13905.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___146_13905.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___146_13905.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___146_13905.FStar_TypeChecker_Env.dsenv)
            } in
          let uu____13906 =
            let uu____13917 =
              let uu____13918 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____13918 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____13917 lb in
          (match uu____13906 with
           | (e1,uu____13940,c1,g1,annotated) ->
               let x =
                 let uu___147_13945 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___147_13945.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___147_13945.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____13946 =
                 let uu____13951 =
                   let uu____13952 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____13952] in
                 FStar_Syntax_Subst.open_term uu____13951 e2 in
               (match uu____13946 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = FStar_Pervasives_Native.fst xbinder in
                    let uu____13971 =
                      let uu____13978 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____13978 e21 in
                    (match uu____13971 with
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
                           let uu____13997 =
                             let uu____14000 =
                               let uu____14001 =
                                 let uu____14014 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____14014) in
                               FStar_Syntax_Syntax.Tm_let uu____14001 in
                             FStar_Syntax_Syntax.mk uu____14000 in
                           uu____13997 FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____14028 =
                             let uu____14029 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____14030 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____14029
                               c1.FStar_Syntax_Syntax.res_typ uu____14030 e11 in
                           FStar_All.pipe_left
                             (fun _0_42  ->
                                FStar_TypeChecker_Common.NonTrivial _0_42)
                             uu____14028 in
                         let g21 =
                           let uu____14032 =
                             let uu____14033 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____14033 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____14032 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____14035 =
                           let uu____14036 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____14036 in
                         if uu____14035
                         then
                           let tt =
                             let uu____14046 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____14046
                               FStar_Option.get in
                           ((let uu____14052 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____14052
                             then
                               let uu____14053 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____14054 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____14053 uu____14054
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape FStar_Pervasives_Native.None
                                env2 [x1] cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____14059 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____14059
                             then
                               let uu____14060 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____14061 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____14060 uu____14061
                             else ());
                            (e4,
                              ((let uu___148_14064 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___148_14064.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___148_14064.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___148_14064.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____14065 -> failwith "Impossible"
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
          let uu____14097 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____14097 with
           | (lbs1,e21) ->
               let uu____14116 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____14116 with
                | (env0,topt) ->
                    let uu____14135 = build_let_rec_env true env0 lbs1 in
                    (match uu____14135 with
                     | (lbs2,rec_env) ->
                         let uu____14154 = check_let_recs rec_env lbs2 in
                         (match uu____14154 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____14174 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____14174
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____14180 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____14180
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
                                     let uu____14229 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____14269 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____14269))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____14229 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____14318  ->
                                           match uu____14318 with
                                           | (x,uvs,e,c,gvs) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____14365 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____14365 in
                              let uu____14370 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                              (match uu____14370 with
                               | (lbs5,e22) ->
                                   ((let uu____14390 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1 in
                                     FStar_All.pipe_right uu____14390
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____14391 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     (uu____14391, cres,
                                       FStar_TypeChecker_Rel.trivial_guard))))))))
      | uu____14404 -> failwith "Impossible"
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
          let uu____14436 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____14436 with
           | (lbs1,e21) ->
               let uu____14455 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____14455 with
                | (env0,topt) ->
                    let uu____14474 = build_let_rec_env false env0 lbs1 in
                    (match uu____14474 with
                     | (lbs2,rec_env) ->
                         let uu____14493 = check_let_recs rec_env lbs2 in
                         (match uu____14493 with
                          | (lbs3,g_lbs) ->
                              let uu____14512 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___149_14535 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___149_14535.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___149_14535.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___150_14537 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___150_14537.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___150_14537.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___150_14537.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___150_14537.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____14512 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____14564 = tc_term env2 e21 in
                                   (match uu____14564 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____14581 =
                                            let uu____14582 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____14582 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____14581 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___151_14586 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___151_14586.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___151_14586.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___151_14586.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____14587 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____14587 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____14623 ->
                                                  (e, cres2, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  let cres3 =
                                                    let uu___152_14628 =
                                                      cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___152_14628.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___152_14628.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___152_14628.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____14631 -> failwith "Impossible"
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
          let uu____14660 = FStar_Options.ml_ish () in
          if uu____14660
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp in
             let uu____14663 =
               let uu____14668 =
                 let uu____14669 = FStar_Syntax_Subst.compress t in
                 uu____14669.FStar_Syntax_Syntax.n in
               let uu____14672 =
                 let uu____14673 = FStar_Syntax_Subst.compress lbdef in
                 uu____14673.FStar_Syntax_Syntax.n in
               (uu____14668, uu____14672) in
             match uu____14663 with
             | (FStar_Syntax_Syntax.Tm_arrow
                (formals,c),FStar_Syntax_Syntax.Tm_abs
                (actuals,uu____14679,uu____14680)) ->
                 let actuals1 =
                   let uu____14718 =
                     FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                   FStar_TypeChecker_Util.maybe_add_implicit_binders
                     uu____14718 actuals in
                 (if
                    (FStar_List.length formals) <>
                      (FStar_List.length actuals1)
                  then
                    (let actuals_msg =
                       let n1 = FStar_List.length actuals1 in
                       if n1 = (Prims.parse_int "1")
                       then "1 argument was found"
                       else
                         (let uu____14739 = FStar_Util.string_of_int n1 in
                          FStar_Util.format1 "%s arguments were found"
                            uu____14739) in
                     let formals_msg =
                       let n1 = FStar_List.length formals in
                       if n1 = (Prims.parse_int "1")
                       then "1 argument"
                       else
                         (let uu____14757 = FStar_Util.string_of_int n1 in
                          FStar_Util.format1 "%s arguments" uu____14757) in
                     let msg =
                       let uu____14765 =
                         FStar_Syntax_Print.term_to_string lbtyp in
                       let uu____14766 =
                         FStar_Syntax_Print.lbname_to_string lbname in
                       FStar_Util.format4
                         "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                         uu____14765 uu____14766 formals_msg actuals_msg in
                     FStar_Exn.raise
                       (FStar_Errors.Error
                          (msg, (lbdef.FStar_Syntax_Syntax.pos))))
                  else ();
                  (let quals =
                     FStar_TypeChecker_Env.lookup_effect_quals env
                       (FStar_Syntax_Util.comp_effect_name c) in
                   FStar_All.pipe_right quals
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
             | uu____14773 ->
                 let uu____14778 =
                   let uu____14779 =
                     let uu____14784 =
                       let uu____14785 =
                         FStar_Syntax_Print.term_to_string lbdef in
                       let uu____14786 =
                         FStar_Syntax_Print.term_to_string lbtyp in
                       FStar_Util.format2
                         "Only function literals with arrow types can be defined recursively; got %s : %s"
                         uu____14785 uu____14786 in
                     (uu____14784, (lbtyp.FStar_Syntax_Syntax.pos)) in
                   FStar_Errors.Error uu____14779 in
                 FStar_Exn.raise uu____14778) in
        let uu____14787 =
          FStar_List.fold_left
            (fun uu____14813  ->
               fun lb  ->
                 match uu____14813 with
                 | (lbs1,env1) ->
                     let uu____14833 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____14833 with
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
                              (let uu____14853 =
                                 let uu____14860 =
                                   let uu____14861 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____14861 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___153_14872 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___153_14872.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___153_14872.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___153_14872.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___153_14872.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___153_14872.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___153_14872.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___153_14872.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___153_14872.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___153_14872.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___153_14872.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___153_14872.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___153_14872.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___153_14872.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___153_14872.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___153_14872.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___153_14872.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___153_14872.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___153_14872.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___153_14872.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___153_14872.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___153_14872.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___153_14872.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___153_14872.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___153_14872.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___153_14872.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___153_14872.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___153_14872.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___153_14872.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___153_14872.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___153_14872.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___153_14872.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___153_14872.FStar_TypeChecker_Env.dsenv)
                                    }) t uu____14860 in
                               match uu____14853 with
                               | (t1,uu____14874,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____14878 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____14878);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____14880 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____14880
                            then
                              let uu___154_14881 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___154_14881.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___154_14881.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___154_14881.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___154_14881.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___154_14881.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___154_14881.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___154_14881.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___154_14881.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___154_14881.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___154_14881.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___154_14881.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___154_14881.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___154_14881.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___154_14881.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___154_14881.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___154_14881.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___154_14881.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___154_14881.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___154_14881.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___154_14881.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___154_14881.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___154_14881.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___154_14881.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___154_14881.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___154_14881.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___154_14881.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___154_14881.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___154_14881.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___154_14881.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___154_14881.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___154_14881.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___154_14881.FStar_TypeChecker_Env.dsenv)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1) in
                          let lb1 =
                            let uu___155_14898 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___155_14898.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___155_14898.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____14787 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lbs  ->
      let uu____14921 =
        let uu____14930 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____14959 =
                     let uu____14960 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____14960.FStar_Syntax_Syntax.n in
                   match uu____14959 with
                   | FStar_Syntax_Syntax.Tm_abs uu____14963 -> ()
                   | uu____14980 ->
                       let uu____14981 =
                         let uu____14982 =
                           let uu____14987 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____14987) in
                         FStar_Errors.Error uu____14982 in
                       FStar_Exn.raise uu____14981);
                  (let uu____14988 =
                     let uu____14995 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____14995
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____14988 with
                   | (e,c,g) ->
                       ((let uu____15004 =
                           let uu____15005 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____15005 in
                         if uu____15004
                         then
                           FStar_Exn.raise
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
        FStar_All.pipe_right uu____14930 FStar_List.unzip in
      match uu____14921 with
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
        let uu____15054 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____15054 with
        | (env1,uu____15072) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____15080 = check_lbtyp top_level env lb in
            (match uu____15080 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Exn.raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____15124 =
                     tc_maybe_toplevel_term
                       (let uu___156_15133 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___156_15133.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___156_15133.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___156_15133.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___156_15133.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___156_15133.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___156_15133.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___156_15133.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___156_15133.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___156_15133.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___156_15133.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___156_15133.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___156_15133.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___156_15133.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___156_15133.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___156_15133.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___156_15133.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___156_15133.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___156_15133.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___156_15133.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.failhard =
                            (uu___156_15133.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___156_15133.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___156_15133.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___156_15133.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___156_15133.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___156_15133.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___156_15133.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___156_15133.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___156_15133.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___156_15133.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___156_15133.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___156_15133.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___156_15133.FStar_TypeChecker_Env.dsenv)
                        }) e11 in
                   match uu____15124 with
                   | (e12,c1,g1) ->
                       let uu____15147 =
                         let uu____15152 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____15156  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____15152 e12 c1 wf_annot in
                       (match uu____15147 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____15171 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____15171
                              then
                                let uu____15172 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____15173 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____15174 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____15172 uu____15173 uu____15174
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
        | uu____15218 ->
            let uu____15219 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____15219 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____15268 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____15268)
                 else
                   (let uu____15276 = FStar_Syntax_Util.type_u () in
                    match uu____15276 with
                    | (k,uu____15296) ->
                        let uu____15297 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____15297 with
                         | (t2,uu____15319,g) ->
                             ((let uu____15322 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____15322
                               then
                                 let uu____15323 =
                                   let uu____15324 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____15324 in
                                 let uu____15325 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____15323 uu____15325
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____15328 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____15328))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun uu____15336  ->
      match uu____15336 with
      | (x,imp) ->
          let uu____15355 = FStar_Syntax_Util.type_u () in
          (match uu____15355 with
           | (tu,u) ->
               ((let uu____15375 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____15375
                 then
                   let uu____15376 = FStar_Syntax_Print.bv_to_string x in
                   let uu____15377 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____15378 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____15376 uu____15377 uu____15378
                 else ());
                (let uu____15380 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____15380 with
                 | (t,uu____15400,g) ->
                     let x1 =
                       ((let uu___157_15408 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___157_15408.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___157_15408.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____15410 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____15410
                       then
                         let uu____15411 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1) in
                         let uu____15412 =
                           FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____15411 uu____15412
                       else ());
                      (let uu____15414 = push_binding env x1 in
                       (x1, uu____15414, g, u))))))
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
            let uu____15504 = tc_binder env1 b in
            (match uu____15504 with
             | (b1,env',g,u) ->
                 let uu____15545 = aux env' bs2 in
                 (match uu____15545 with
                  | (bs3,env'1,g',us) ->
                      let uu____15598 =
                        let uu____15599 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____15599 in
                      ((b1 :: bs3), env'1, uu____15598, (u :: us)))) in
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
          (fun uu____15684  ->
             fun uu____15685  ->
               match (uu____15684, uu____15685) with
               | ((t,imp),(args1,g)) ->
                   let uu____15754 = tc_term env1 t in
                   (match uu____15754 with
                    | (t1,uu____15772,g') ->
                        let uu____15774 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____15774))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____15816  ->
             match uu____15816 with
             | (pats1,g) ->
                 let uu____15841 = tc_args env p in
                 (match uu____15841 with
                  | (args,g') ->
                      let uu____15854 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____15854))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let uu____15867 = tc_maybe_toplevel_term env e in
      match uu____15867 with
      | (e1,c,g) ->
          let uu____15883 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____15883
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____15896 =
               let uu____15901 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____15901
               then
                 let uu____15906 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____15906, false)
               else
                 (let uu____15908 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____15908, true)) in
             match uu____15896 with
             | (target_comp,allow_ghost) ->
                 let uu____15917 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____15917 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____15927 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____15927)
                  | uu____15928 ->
                      if allow_ghost
                      then
                        let uu____15937 =
                          let uu____15938 =
                            let uu____15943 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____15943, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____15938 in
                        FStar_Exn.raise uu____15937
                      else
                        (let uu____15951 =
                           let uu____15952 =
                             let uu____15957 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____15957, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____15952 in
                         FStar_Exn.raise uu____15951)))
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
      let uu____15976 = tc_tot_or_gtot_term env t in
      match uu____15976 with
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
      (let uu____16006 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____16006
       then
         let uu____16007 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____16007
       else ());
      (let env1 =
         let uu___158_16010 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___158_16010.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___158_16010.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___158_16010.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___158_16010.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___158_16010.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___158_16010.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___158_16010.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___158_16010.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___158_16010.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___158_16010.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___158_16010.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___158_16010.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___158_16010.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___158_16010.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___158_16010.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___158_16010.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___158_16010.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___158_16010.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___158_16010.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___158_16010.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___158_16010.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___158_16010.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___158_16010.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___158_16010.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___158_16010.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___158_16010.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___158_16010.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___158_16010.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___158_16010.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___158_16010.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___158_16010.FStar_TypeChecker_Env.dsenv)
         } in
       let uu____16015 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____16048) ->
             let uu____16049 =
               let uu____16050 =
                 let uu____16055 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____16055) in
               FStar_Errors.Error uu____16050 in
             FStar_Exn.raise uu____16049 in
       match uu____16015 with
       | (t,c,g) ->
           let uu____16071 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____16071
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____16081 =
                let uu____16082 =
                  let uu____16087 =
                    let uu____16088 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____16088 in
                  let uu____16089 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____16087, uu____16089) in
                FStar_Errors.Error uu____16082 in
              FStar_Exn.raise uu____16081))
let level_of_type_fail:
  'Auu____16104 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____16104
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____16117 =
          let uu____16118 =
            let uu____16123 =
              let uu____16124 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format2
                "Expected a term of type 'Type'; got %s : %s" uu____16124 t in
            let uu____16125 = FStar_TypeChecker_Env.get_range env in
            (uu____16123, uu____16125) in
          FStar_Errors.Error uu____16118 in
        FStar_Exn.raise uu____16117
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____16145 =
            let uu____16146 = FStar_Syntax_Util.unrefine t1 in
            uu____16146.FStar_Syntax_Syntax.n in
          match uu____16145 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____16150 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____16153 = FStar_Syntax_Util.type_u () in
                 match uu____16153 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___161_16161 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___161_16161.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___161_16161.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___161_16161.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___161_16161.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___161_16161.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___161_16161.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___161_16161.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___161_16161.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___161_16161.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___161_16161.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___161_16161.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___161_16161.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___161_16161.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___161_16161.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___161_16161.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___161_16161.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___161_16161.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___161_16161.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___161_16161.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___161_16161.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___161_16161.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___161_16161.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___161_16161.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___161_16161.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___161_16161.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___161_16161.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___161_16161.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___161_16161.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___161_16161.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___161_16161.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___161_16161.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___161_16161.FStar_TypeChecker_Env.dsenv)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____16165 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____16165
                       | uu____16166 ->
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
      let uu____16177 =
        let uu____16178 = FStar_Syntax_Subst.compress e in
        uu____16178.FStar_Syntax_Syntax.n in
      match uu____16177 with
      | FStar_Syntax_Syntax.Tm_bvar uu____16183 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____16188 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____16215 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____16231) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____16254,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____16281) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____16288 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____16288 with | ((uu____16299,t),uu____16301) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16306,(FStar_Util.Inl t,uu____16308),uu____16309) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16356,(FStar_Util.Inr c,uu____16358),uu____16359) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____16409;
             FStar_Syntax_Syntax.vars = uu____16410;_},us)
          ->
          let uu____16416 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____16416 with
           | ((us',t),uu____16429) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____16435 =
                     let uu____16436 =
                       let uu____16441 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____16441) in
                     FStar_Errors.Error uu____16436 in
                   FStar_Exn.raise uu____16435)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____16457 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____16458 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____16468) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____16491 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____16491 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____16511  ->
                      match uu____16511 with
                      | (b,uu____16517) ->
                          let uu____16518 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____16518) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____16523 = universe_of_aux env res in
                 level_of_type env res uu____16523 in
               let u_c =
                 let uu____16525 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____16525 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____16529 = universe_of_aux env trepr in
                     level_of_type env trepr uu____16529 in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____16622 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____16637 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____16676 ->
                let uu____16677 = universe_of_aux env hd3 in
                (uu____16677, args1)
            | FStar_Syntax_Syntax.Tm_name uu____16690 ->
                let uu____16691 = universe_of_aux env hd3 in
                (uu____16691, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____16704 ->
                let uu____16721 = universe_of_aux env hd3 in
                (uu____16721, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____16734 ->
                let uu____16741 = universe_of_aux env hd3 in
                (uu____16741, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____16754 ->
                let uu____16781 = universe_of_aux env hd3 in
                (uu____16781, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____16794 ->
                let uu____16801 = universe_of_aux env hd3 in
                (uu____16801, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____16814 ->
                let uu____16815 = universe_of_aux env hd3 in
                (uu____16815, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____16828 ->
                let uu____16841 = universe_of_aux env hd3 in
                (uu____16841, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____16854 ->
                let uu____16861 = universe_of_aux env hd3 in
                (uu____16861, args1)
            | FStar_Syntax_Syntax.Tm_type uu____16874 ->
                let uu____16875 = universe_of_aux env hd3 in
                (uu____16875, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____16888,hd4::uu____16890) ->
                let uu____16955 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____16955 with
                 | (uu____16970,uu____16971,hd5) ->
                     let uu____16989 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____16989 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____17040 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____17042 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____17042 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____17093 ->
                let uu____17094 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____17094 with
                 | (env1,uu____17116) ->
                     let env2 =
                       let uu___162_17122 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___162_17122.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___162_17122.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___162_17122.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___162_17122.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___162_17122.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___162_17122.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___162_17122.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___162_17122.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___162_17122.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___162_17122.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___162_17122.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___162_17122.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___162_17122.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___162_17122.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___162_17122.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___162_17122.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___162_17122.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___162_17122.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___162_17122.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___162_17122.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___162_17122.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___162_17122.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___162_17122.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___162_17122.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___162_17122.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___162_17122.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___162_17122.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___162_17122.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___162_17122.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___162_17122.FStar_TypeChecker_Env.dsenv)
                       } in
                     ((let uu____17124 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____17124
                       then
                         let uu____17125 =
                           let uu____17126 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____17126 in
                         let uu____17127 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____17125 uu____17127
                       else ());
                      (let uu____17129 = tc_term env2 hd3 in
                       match uu____17129 with
                       | (uu____17150,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____17151;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____17153;
                                        FStar_Syntax_Syntax.comp =
                                          uu____17154;_},g)
                           ->
                           ((let uu____17165 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____17165
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____17176 = type_of_head true hd1 args in
          (match uu____17176 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____17216 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____17216 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____17260 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____17260)))
      | FStar_Syntax_Syntax.Tm_match (uu____17263,hd1::uu____17265) ->
          let uu____17330 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____17330 with
           | (uu____17333,uu____17334,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____17352,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____17397 = universe_of_aux env e in
      level_of_type env e uu____17397
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tps  ->
      let uu____17418 = tc_binders env tps in
      match uu____17418 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))