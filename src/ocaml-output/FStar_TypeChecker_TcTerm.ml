open Prims
let instantiate_both: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___336_4 = env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___336_4.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___336_4.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___336_4.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___336_4.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___336_4.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___336_4.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___336_4.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___336_4.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___336_4.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___336_4.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___336_4.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___336_4.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___336_4.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___336_4.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___336_4.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___336_4.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___336_4.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___336_4.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___336_4.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___336_4.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___336_4.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___336_4.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___336_4.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___336_4.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___336_4.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___336_4.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___336_4.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___336_4.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___336_4.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___336_4.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___336_4.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___336_4.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___336_4.FStar_TypeChecker_Env.dep_graph)
    }
let no_inst: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___337_8 = env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___337_8.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___337_8.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___337_8.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___337_8.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___337_8.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___337_8.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___337_8.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___337_8.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___337_8.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___337_8.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___337_8.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___337_8.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___337_8.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___337_8.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___337_8.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___337_8.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___337_8.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___337_8.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___337_8.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___337_8.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___337_8.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___337_8.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___337_8.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___337_8.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___337_8.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___337_8.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___337_8.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___337_8.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___337_8.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___337_8.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___337_8.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___337_8.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___337_8.FStar_TypeChecker_Env.dep_graph)
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
  fun uu___331_53  ->
    match uu___331_53 with
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
                          let uu____131 =
                            let uu____132 =
                              let uu____137 =
                                FStar_TypeChecker_Env.get_range env in
                              (msg, uu____137) in
                            FStar_Errors.Error uu____132 in
                          FStar_Exn.raise uu____131 in
                        let s =
                          let uu____139 =
                            let uu____140 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____140 in
                          FStar_TypeChecker_Util.new_uvar env uu____139 in
                        let uu____149 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s in
                        match uu____149 with
                        | FStar_Pervasives_Native.Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____154 -> fail ())) in
          aux false kt
let push_binding:
  'Auu____160 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____160) FStar_Pervasives_Native.tuple2 ->
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
        let uu____190 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____190
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
      let uu___338_204 = lc in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___338_204.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags =
          (uu___338_204.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____207  ->
             let uu____208 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Util.set_result_typ uu____208 t)
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
            let uu____253 =
              let uu____254 = FStar_Syntax_Subst.compress t in
              uu____254.FStar_Syntax_Syntax.n in
            match uu____253 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____257,c) ->
                let uu____275 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c) in
                if uu____275
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c) in
                  let uu____277 =
                    let uu____278 = FStar_Syntax_Subst.compress t1 in
                    uu____278.FStar_Syntax_Syntax.n in
                  (match uu____277 with
                   | FStar_Syntax_Syntax.Tm_constant uu____281 -> false
                   | uu____282 ->
                       let uu____283 = FStar_Syntax_Util.is_unit t1 in
                       Prims.op_Negation uu____283)
                else false
            | uu____285 ->
                let uu____286 = FStar_Syntax_Util.is_unit t in
                Prims.op_Negation uu____286 in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____289 =
                  let uu____292 =
                    (let uu____295 = should_return t in
                     Prims.op_Negation uu____295) ||
                      (let uu____297 =
                         FStar_TypeChecker_Env.should_verify env in
                       Prims.op_Negation uu____297) in
                  if uu____292
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e in
                FStar_Syntax_Util.lcomp_of_comp uu____289
            | FStar_Util.Inr lc -> lc in
          let t = lc.FStar_Syntax_Syntax.res_typ in
          let uu____305 =
            let uu____312 = FStar_TypeChecker_Env.expected_typ env in
            match uu____312 with
            | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                ((let uu____323 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High in
                  if uu____323
                  then
                    let uu____324 = FStar_Syntax_Print.term_to_string t in
                    let uu____325 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____324
                      uu____325
                  else ());
                 (let uu____327 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t' in
                  match uu____327 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____343 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____343 with
                       | (e2,g) ->
                           ((let uu____357 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____357
                             then
                               let uu____358 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____359 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____360 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____361 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____358 uu____359 uu____360 uu____361
                             else ());
                            (let msg =
                               let uu____368 =
                                 FStar_TypeChecker_Rel.is_trivial g in
                               if uu____368
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_40  ->
                                      FStar_Pervasives_Native.Some _0_40)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             let uu____385 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1 in
                             match uu____385 with
                             | (lc2,g2) ->
                                 ((memo_tk e2 t'), (set_lcomp_result lc2 t'),
                                   g2)))))) in
          match uu____305 with
          | (e1,lc1,g) ->
              ((let uu____408 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low in
                if uu____408
                then
                  let uu____409 = FStar_Syntax_Print.lcomp_to_string lc1 in
                  FStar_Util.print1 "Return comp type is %s\n" uu____409
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
        let uu____432 = FStar_TypeChecker_Env.expected_typ env in
        match uu____432 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____442 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____442 with
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
      fun uu____475  ->
        match uu____475 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____504 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____504
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____506 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____506
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____508 =
              match copt with
              | FStar_Pervasives_Native.Some uu____521 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____524 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____526 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____526)) in
                  if uu____524
                  then
                    let uu____533 =
                      let uu____536 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos in
                      FStar_Pervasives_Native.Some uu____536 in
                    (uu____533, c)
                  else
                    (let uu____540 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____540
                     then
                       let uu____547 = tot_or_gtot c in
                       (FStar_Pervasives_Native.None, uu____547)
                     else
                       (let uu____551 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____551
                        then
                          let uu____558 =
                            let uu____561 = tot_or_gtot c in
                            FStar_Pervasives_Native.Some uu____561 in
                          (uu____558, c)
                        else (FStar_Pervasives_Native.None, c))) in
            (match uu____508 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let uu____587 =
                        FStar_TypeChecker_Util.check_comp env e c2 expected_c in
                      (match uu____587 with
                       | (e1,uu____601,g) ->
                           let g1 =
                             let uu____604 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_TypeChecker_Util.label_guard uu____604
                               "could not prove post-condition" g in
                           ((let uu____606 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low in
                             if uu____606
                             then
                               let uu____607 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos in
                               let uu____608 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1 in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____607 uu____608
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c2)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c2) in
                             (e2, expected_c, g1))))))
let no_logical_guard:
  'Auu____615 'Auu____616 .
    FStar_TypeChecker_Env.env ->
      ('Auu____616,'Auu____615,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____616,'Auu____615,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____636  ->
      match uu____636 with
      | (te,kt,f) ->
          let uu____646 = FStar_TypeChecker_Rel.guard_form f in
          (match uu____646 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____654 =
                 let uu____655 =
                   let uu____660 =
                     FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                       env f1 in
                   let uu____661 = FStar_TypeChecker_Env.get_range env in
                   (uu____660, uu____661) in
                 FStar_Errors.Error uu____655 in
               FStar_Exn.raise uu____654)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____671 = FStar_TypeChecker_Env.expected_typ env in
    match uu____671 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____675 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____675
let rec get_pat_vars:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun pats  ->
    fun acc  ->
      let pats1 = FStar_Syntax_Util.unmeta pats in
      let uu____699 = FStar_Syntax_Util.head_and_args pats1 in
      match uu____699 with
      | (head1,args) ->
          let uu____738 =
            let uu____739 = FStar_Syntax_Util.un_uinst head1 in
            uu____739.FStar_Syntax_Syntax.n in
          (match uu____738 with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid
               ->
               let uu____746 = FStar_List.tl args in
               get_pat_vars_args uu____746 acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.smtpatOr_lid
               -> get_pat_vars_args args acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               -> get_pat_vars_args args acc
           | uu____755 ->
               let uu____756 = FStar_Syntax_Free.names pats1 in
               FStar_Util.set_union acc uu____756)
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
  'Auu____786 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,'Auu____786) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____819 = FStar_Syntax_Util.is_smt_lemma t in
          if uu____819
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____820;
                  FStar_Syntax_Syntax.effect_name = uu____821;
                  FStar_Syntax_Syntax.result_typ = uu____822;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____826)::[];
                  FStar_Syntax_Syntax.flags = uu____827;_}
                ->
                let pat_vars =
                  let uu____875 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta] env pats in
                  let uu____876 =
                    FStar_Util.new_set FStar_Syntax_Syntax.order_bv in
                  get_pat_vars uu____875 uu____876 in
                let uu____879 =
                  FStar_All.pipe_right bs
                    (FStar_Util.find_opt
                       (fun uu____906  ->
                          match uu____906 with
                          | (b,uu____912) ->
                              let uu____913 = FStar_Util.set_mem b pat_vars in
                              Prims.op_Negation uu____913)) in
                (match uu____879 with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some (x,uu____919) ->
                     let uu____924 =
                       let uu____925 = FStar_Syntax_Print.bv_to_string x in
                       FStar_Util.format1
                         "Pattern misses at least one bound variable: %s"
                         uu____925 in
                     FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____924)
            | uu____926 -> failwith "Impossible"
          else ()
let guard_letrecs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
          FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        let uu____957 =
          let uu____958 = FStar_TypeChecker_Env.should_verify env in
          Prims.op_Negation uu____958 in
        if uu____957
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env in
               let env1 =
                 let uu___339_999 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___339_999.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___339_999.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___339_999.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___339_999.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___339_999.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___339_999.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___339_999.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___339_999.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___339_999.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___339_999.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___339_999.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___339_999.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___339_999.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___339_999.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___339_999.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___339_999.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___339_999.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___339_999.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___339_999.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___339_999.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___339_999.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___339_999.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___339_999.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___339_999.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___339_999.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___339_999.FStar_TypeChecker_Env.qname_and_index);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___339_999.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth =
                     (uu___339_999.FStar_TypeChecker_Env.synth);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___339_999.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___339_999.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___339_999.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___339_999.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___339_999.FStar_TypeChecker_Env.dep_graph)
                 } in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Parser_Const.precedes_lid in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____1035  ->
                           match uu____1035 with
                           | (b,uu____1043) ->
                               let t =
                                 let uu____1045 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort in
                                 FStar_TypeChecker_Normalize.unfold_whnf env1
                                   uu____1045 in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type uu____1048 ->
                                    []
                                | FStar_Syntax_Syntax.Tm_arrow uu____1049 ->
                                    []
                                | uu____1062 ->
                                    let uu____1063 =
                                      FStar_Syntax_Syntax.bv_to_name b in
                                    [uu____1063]))) in
                 let as_lex_list dec =
                   let uu____1068 = FStar_Syntax_Util.head_and_args dec in
                   match uu____1068 with
                   | (head1,uu____1084) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.lexcons_lid
                            -> dec
                        | uu____1106 -> mk_lex_list [dec]) in
                 let cflags = FStar_Syntax_Util.comp_flags c in
                 let uu____1110 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___332_1119  ->
                           match uu___332_1119 with
                           | FStar_Syntax_Syntax.DECREASES uu____1120 -> true
                           | uu____1123 -> false)) in
                 match uu____1110 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.DECREASES dec) -> as_lex_list dec
                 | uu____1127 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions in
                     (match xs with
                      | x::[] -> x
                      | uu____1136 -> mk_lex_list xs) in
               let previous_dec = decreases_clause actuals expected_c in
               let guard_one_letrec uu____1157 =
                 match uu____1157 with
                 | (l,t,u_names) ->
                     let uu____1175 =
                       let uu____1176 = FStar_Syntax_Subst.compress t in
                       uu____1176.FStar_Syntax_Syntax.n in
                     (match uu____1175 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____1237  ->
                                    match uu____1237 with
                                    | (x,imp) ->
                                        let uu____1248 =
                                          FStar_Syntax_Syntax.is_null_bv x in
                                        if uu____1248
                                        then
                                          let uu____1253 =
                                            let uu____1254 =
                                              let uu____1257 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x in
                                              FStar_Pervasives_Native.Some
                                                uu____1257 in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____1254
                                              x.FStar_Syntax_Syntax.sort in
                                          (uu____1253, imp)
                                        else (x, imp))) in
                          let uu____1259 =
                            FStar_Syntax_Subst.open_comp formals1 c in
                          (match uu____1259 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1 in
                               let precedes1 =
                                 let uu____1278 =
                                   let uu____1279 =
                                     let uu____1280 =
                                       FStar_Syntax_Syntax.as_arg dec in
                                     let uu____1281 =
                                       let uu____1284 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec in
                                       [uu____1284] in
                                     uu____1280 :: uu____1281 in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____1279 in
                                 uu____1278 FStar_Pervasives_Native.None r in
                               let uu____1287 = FStar_Util.prefix formals2 in
                               (match uu____1287 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___340_1334 = last1 in
                                      let uu____1335 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1 in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___340_1334.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___340_1334.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____1335
                                      } in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)] in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1 in
                                    ((let uu____1361 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low in
                                      if uu____1361
                                      then
                                        let uu____1362 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l in
                                        let uu____1363 =
                                          FStar_Syntax_Print.term_to_string t in
                                        let uu____1364 =
                                          FStar_Syntax_Print.term_to_string
                                            t' in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____1362 uu____1363 uu____1364
                                      else ());
                                     (l, t', u_names))))
                      | uu____1368 ->
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
        (let uu___341_1809 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___341_1809.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___341_1809.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___341_1809.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___341_1809.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___341_1809.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___341_1809.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___341_1809.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___341_1809.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___341_1809.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___341_1809.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___341_1809.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___341_1809.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___341_1809.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___341_1809.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___341_1809.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___341_1809.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___341_1809.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___341_1809.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___341_1809.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___341_1809.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___341_1809.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___341_1809.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___341_1809.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___341_1809.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___341_1809.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___341_1809.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___341_1809.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___341_1809.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___341_1809.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___341_1809.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___341_1809.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___341_1809.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___341_1809.FStar_TypeChecker_Env.dep_graph)
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
      (let uu____1821 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1821
       then
         let uu____1822 =
           let uu____1823 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1823 in
         let uu____1824 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1822 uu____1824
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1833 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1864 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1871 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1888 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1889 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1890 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1891 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1892 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1909 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1922 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1929 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____1930;
              FStar_Syntax_Syntax.vars = uu____1931;_},FStar_Syntax_Syntax.Meta_alien
            (uu____1932,uu____1933,ty))
           ->
           let uu____1943 =
             let uu____1944 = FStar_Syntax_Syntax.mk_Total ty in
             FStar_All.pipe_right uu____1944 FStar_Syntax_Util.lcomp_of_comp in
           (top, uu____1943, FStar_TypeChecker_Rel.trivial_guard)
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1950 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1950 with
            | (e2,c,g) ->
                let g1 =
                  let uu___342_1967 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___342_1967.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___342_1967.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___342_1967.FStar_TypeChecker_Env.implicits)
                  } in
                let uu____1968 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (uu____1968, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1989 = FStar_Syntax_Util.type_u () in
           (match uu____1989 with
            | (t,u) ->
                let uu____2002 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____2002 with
                 | (e2,c,g) ->
                     let uu____2018 =
                       let uu____2033 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____2033 with
                       | (env2,uu____2055) -> tc_pats env2 pats in
                     (match uu____2018 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___343_2089 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___343_2089.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___343_2089.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___343_2089.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____2090 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____2093 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____2090, c, uu____2093))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____2101 =
             let uu____2102 = FStar_Syntax_Subst.compress e1 in
             uu____2102.FStar_Syntax_Syntax.n in
           (match uu____2101 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____2111,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____2113;
                               FStar_Syntax_Syntax.lbtyp = uu____2114;
                               FStar_Syntax_Syntax.lbeff = uu____2115;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____2140 =
                  let uu____2147 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit in
                  tc_term uu____2147 e11 in
                (match uu____2140 with
                 | (e12,c1,g1) ->
                     let uu____2157 = tc_term env1 e2 in
                     (match uu____2157 with
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
                            let uu____2181 =
                              let uu____2184 =
                                let uu____2185 =
                                  let uu____2198 =
                                    let uu____2205 =
                                      let uu____2208 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13) in
                                      [uu____2208] in
                                    (false, uu____2205) in
                                  (uu____2198, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____2185 in
                              FStar_Syntax_Syntax.mk uu____2184 in
                            uu____2181 FStar_Pervasives_Native.None
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
                          let uu____2230 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____2230)))
            | uu____2233 ->
                let uu____2234 = tc_term env1 e1 in
                (match uu____2234 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2256) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____2273 = tc_term env1 e1 in
           (match uu____2273 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____2297) ->
           let uu____2344 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2344 with
            | (env0,uu____2358) ->
                let uu____2363 = tc_comp env0 expected_c in
                (match uu____2363 with
                 | (expected_c1,uu____2377,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____2382 =
                       let uu____2389 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____2389 e1 in
                     (match uu____2382 with
                      | (e2,c',g') ->
                          let uu____2399 =
                            let uu____2406 =
                              let uu____2411 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____2411) in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____2406 in
                          (match uu____2399 with
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
                                 let uu____2466 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____2466 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____2475 =
                                            FStar_Syntax_Util.mk_squash f1 in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____2475) in
                               let uu____2476 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____2476 with
                                | (e5,c,f2) ->
                                    let final_guard =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, final_guard))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____2496) ->
           let uu____2543 = FStar_Syntax_Util.type_u () in
           (match uu____2543 with
            | (k,u) ->
                let uu____2556 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____2556 with
                 | (t1,uu____2570,f) ->
                     let uu____2572 =
                       let uu____2579 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____2579 e1 in
                     (match uu____2572 with
                      | (e2,c,g) ->
                          let uu____2589 =
                            let uu____2594 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____2598  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____2594 e2 c f in
                          (match uu____2589 with
                           | (c1,f1) ->
                               let uu____2607 =
                                 let uu____2614 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2,
                                          ((FStar_Util.Inl t1),
                                            FStar_Pervasives_Native.None),
                                          (FStar_Pervasives_Native.Some
                                             (c1.FStar_Syntax_Syntax.eff_name))))
                                     FStar_Pervasives_Native.None
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____2614 c1 in
                               (match uu____2607 with
                                | (e3,c2,f2) ->
                                    let uu____2654 =
                                      let uu____2655 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____2655 in
                                    (e3, c2, uu____2654))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____2656;
              FStar_Syntax_Syntax.vars = uu____2657;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2720 = FStar_Syntax_Util.head_and_args top in
           (match uu____2720 with
            | (unary_op,uu____2742) ->
                let head1 =
                  let uu____2766 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2766 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____2804;
              FStar_Syntax_Syntax.vars = uu____2805;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2868 = FStar_Syntax_Util.head_and_args top in
           (match uu____2868 with
            | (unary_op,uu____2890) ->
                let head1 =
                  let uu____2914 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2914 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____2952);
              FStar_Syntax_Syntax.pos = uu____2953;
              FStar_Syntax_Syntax.vars = uu____2954;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____3017 = FStar_Syntax_Util.head_and_args top in
           (match uu____3017 with
            | (unary_op,uu____3039) ->
                let head1 =
                  let uu____3063 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3063 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3101;
              FStar_Syntax_Syntax.vars = uu____3102;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____3178 = FStar_Syntax_Util.head_and_args top in
           (match uu____3178 with
            | (unary_op,uu____3200) ->
                let head1 =
                  let uu____3224 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____3224 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3268;
              FStar_Syntax_Syntax.vars = uu____3269;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____3307 =
             let uu____3314 =
               let uu____3315 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3315 in
             tc_term uu____3314 e1 in
           (match uu____3307 with
            | (e2,c,g) ->
                let uu____3339 = FStar_Syntax_Util.head_and_args top in
                (match uu____3339 with
                 | (head1,uu____3361) ->
                     let uu____3382 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos in
                     let uu____3409 =
                       let uu____3410 =
                         let uu____3413 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid in
                         FStar_Syntax_Syntax.mk_Total uu____3413 in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____3410 in
                     (uu____3382, uu____3409, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3418;
              FStar_Syntax_Syntax.vars = uu____3419;_},(a1,FStar_Pervasives_Native.None
                                                        )::(a2,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____3472 = FStar_Syntax_Util.head_and_args top in
           (match uu____3472 with
            | (head1,uu____3494) ->
                let env' =
                  let uu____3516 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____3516 in
                let uu____3517 = tc_term env' a1 in
                (match uu____3517 with
                 | (e1,uu____3531,g1) ->
                     let uu____3533 = tc_term env1 a2 in
                     (match uu____3533 with
                      | (e2,t2,g2) ->
                          let g = FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          let uu____3550 =
                            let uu____3553 =
                              let uu____3554 =
                                let uu____3555 =
                                  FStar_Syntax_Syntax.as_arg a1 in
                                let uu____3556 =
                                  let uu____3559 =
                                    FStar_Syntax_Syntax.as_arg a2 in
                                  [uu____3559] in
                                uu____3555 :: uu____3556 in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____3554 in
                            uu____3553 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          (uu____3550, t2, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3564;
              FStar_Syntax_Syntax.vars = uu____3565;_},uu____3566)
           ->
           let uu____3587 =
             let uu____3588 =
               let uu____3593 =
                 let uu____3594 = FStar_Syntax_Print.term_to_string top in
                 FStar_Util.format1 "Ill-applied constant %s" uu____3594 in
               (uu____3593, (e.FStar_Syntax_Syntax.pos)) in
             FStar_Errors.Error uu____3588 in
           FStar_Exn.raise uu____3587
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3601;
              FStar_Syntax_Syntax.vars = uu____3602;_},uu____3603)
           ->
           let uu____3624 =
             let uu____3625 =
               let uu____3630 =
                 let uu____3631 = FStar_Syntax_Print.term_to_string top in
                 FStar_Util.format1 "Ill-applied constant %s" uu____3631 in
               (uu____3630, (e.FStar_Syntax_Syntax.pos)) in
             FStar_Errors.Error uu____3625 in
           FStar_Exn.raise uu____3624
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____3638;
              FStar_Syntax_Syntax.vars = uu____3639;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____3672 =
               let uu____3679 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____3679 with | (env0,uu____3693) -> tc_term env0 e1 in
             match uu____3672 with
             | (e2,c,g) ->
                 let uu____3707 = FStar_Syntax_Util.head_and_args top in
                 (match uu____3707 with
                  | (reify_op,uu____3729) ->
                      let u_c =
                        let uu____3751 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____3751 with
                        | (uu____3758,c',uu____3760) ->
                            let uu____3761 =
                              let uu____3762 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____3762.FStar_Syntax_Syntax.n in
                            (match uu____3761 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____3766 ->
                                 let uu____3767 = FStar_Syntax_Util.type_u () in
                                 (match uu____3767 with
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
                                            let uu____3779 =
                                              let uu____3780 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____3781 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____3782 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____3780 uu____3781
                                                uu____3782 in
                                            failwith uu____3779);
                                       u))) in
                      let repr =
                        let uu____3784 = c.FStar_Syntax_Syntax.comp () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____3784 u_c in
                      let e3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (reify_op, [(e2, aqual)]))
                          FStar_Pervasives_Native.None
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____3805 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____3805
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____3806 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____3806 with
                       | (e4,c2,g') ->
                           let uu____3822 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____3822)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____3824;
              FStar_Syntax_Syntax.vars = uu____3825;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____3867 =
               let uu____3868 =
                 let uu____3869 =
                   let uu____3874 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____3874, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____3869 in
               FStar_Exn.raise uu____3868 in
             let uu____3881 = FStar_Syntax_Util.head_and_args top in
             match uu____3881 with
             | (reflect_op,uu____3903) ->
                 let uu____3924 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____3924 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____3957 =
                        let uu____3958 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____3958 in
                      if uu____3957
                      then no_reflect ()
                      else
                        (let uu____3968 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____3968 with
                         | (env_no_ex,topt) ->
                             let uu____3987 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____4007 =
                                   let uu____4010 =
                                     let uu____4011 =
                                       let uu____4026 =
                                         let uu____4029 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____4030 =
                                           let uu____4033 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____4033] in
                                         uu____4029 :: uu____4030 in
                                       (repr, uu____4026) in
                                     FStar_Syntax_Syntax.Tm_app uu____4011 in
                                   FStar_Syntax_Syntax.mk uu____4010 in
                                 uu____4007 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos in
                               let uu____4039 =
                                 let uu____4046 =
                                   let uu____4047 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____4047
                                     FStar_Pervasives_Native.fst in
                                 tc_tot_or_gtot_term uu____4046 t in
                               match uu____4039 with
                               | (t1,uu____4075,g) ->
                                   let uu____4077 =
                                     let uu____4078 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____4078.FStar_Syntax_Syntax.n in
                                   (match uu____4077 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____4093,(res,uu____4095)::
                                         (wp,uu____4097)::[])
                                        -> (t1, res, wp, g)
                                    | uu____4140 -> failwith "Impossible") in
                             (match uu____3987 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____4171 =
                                    let uu____4176 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____4176 with
                                    | (e2,c,g) ->
                                        ((let uu____4191 =
                                            let uu____4192 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____4192 in
                                          if uu____4191
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____4202 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____4202 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____4210 =
                                                  let uu____4217 =
                                                    let uu____4222 =
                                                      let uu____4223 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____4224 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____4223 uu____4224 in
                                                    (uu____4222,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____4217] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____4210);
                                               (let uu____4233 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____4233)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____4235 =
                                                let uu____4236 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____4236 in
                                              (e2, uu____4235))) in
                                  (match uu____4171 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____4246 =
                                           let uu____4247 =
                                             let uu____4248 =
                                               let uu____4249 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____4249] in
                                             let uu____4250 =
                                               let uu____4259 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____4259] in
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
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____4247 in
                                         FStar_All.pipe_right uu____4246
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____4279 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____4279 with
                                        | (e4,c1,g') ->
                                            let uu____4295 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____4295))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____4342 =
               let uu____4343 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____4343 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____4342 instantiate_both in
           ((let uu____4359 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____4359
             then
               let uu____4360 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____4361 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____4360
                 uu____4361
             else ());
            (let isquote =
               let uu____4364 = FStar_Syntax_Util.head_and_args head1 in
               match uu____4364 with
               | (head2,uu____4380) ->
                   let uu____4401 =
                     let uu____4402 = FStar_Syntax_Util.un_uinst head2 in
                     uu____4402.FStar_Syntax_Syntax.n in
                   (match uu____4401 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.quote_lid
                        -> true
                    | uu____4406 -> false) in
             let uu____4407 = tc_term (no_inst env2) head1 in
             match uu____4407 with
             | (head2,chead,g_head) ->
                 let uu____4423 =
                   let uu____4430 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____4430
                   then
                     let uu____4437 =
                       let uu____4444 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____4444 in
                     match uu____4437 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____4457 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____4459 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c in
                                 Prims.op_Negation uu____4459))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                           if uu____4457
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c in
                         (e1, c1, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2 in
                      let uu____4464 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env3 head2 chead g_head args
                        uu____4464) in
                 (match uu____4423 with
                  | (e1,c,g) ->
                      ((let uu____4477 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____4477
                        then
                          let uu____4478 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____4478
                        else ());
                       (let uu____4480 = comp_check_expected_typ env0 e1 c in
                        match uu____4480 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____4497 =
                                let uu____4498 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____4498.FStar_Syntax_Syntax.n in
                              match uu____4497 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____4502) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___344_4564 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___344_4564.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___344_4564.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___344_4564.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____4613 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____4615 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____4615 in
                            ((let uu____4617 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____4617
                              then
                                let uu____4618 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____4619 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____4618 uu____4619
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____4659 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____4659 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____4679 = tc_term env12 e1 in
                (match uu____4679 with
                 | (e11,c1,g1) ->
                     let uu____4695 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____4705 = FStar_Syntax_Util.type_u () in
                           (match uu____4705 with
                            | (k,uu____4715) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____4717 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____4717, res_t)) in
                     (match uu____4695 with
                      | (env_branches,res_t) ->
                          ((let uu____4727 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____4727
                            then
                              let uu____4728 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____4728
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____4814 =
                              let uu____4819 =
                                FStar_List.fold_right
                                  (fun uu____4865  ->
                                     fun uu____4866  ->
                                       match (uu____4865, uu____4866) with
                                       | ((uu____4929,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____4989 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____4989))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____4819 with
                              | (cases,g) ->
                                  let uu____5028 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____5028, g) in
                            match uu____4814 with
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
                                           (fun uu____5124  ->
                                              match uu____5124 with
                                              | ((pat,wopt,br),uu____5152,lc,uu____5154)
                                                  ->
                                                  let uu____5167 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____5167))) in
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
                                  let uu____5222 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____5222
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____5229 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____5229 in
                                     let lb =
                                       let uu____5233 =
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
                                           uu____5233;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____5237 =
                                         let uu____5240 =
                                           let uu____5241 =
                                             let uu____5254 =
                                               let uu____5255 =
                                                 let uu____5256 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____5256] in
                                               FStar_Syntax_Subst.close
                                                 uu____5255 e_match in
                                             ((false, [lb]), uu____5254) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____5241 in
                                         FStar_Syntax_Syntax.mk uu____5240 in
                                       uu____5237
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____5269 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____5269
                                  then
                                    let uu____5270 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____5271 =
                                      let uu____5272 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____5272 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____5270 uu____5271
                                  else ());
                                 (let uu____5274 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____5274))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5277;
                FStar_Syntax_Syntax.lbunivs = uu____5278;
                FStar_Syntax_Syntax.lbtyp = uu____5279;
                FStar_Syntax_Syntax.lbeff = uu____5280;
                FStar_Syntax_Syntax.lbdef = uu____5281;_}::[]),uu____5282)
           ->
           ((let uu____5302 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5302
             then
               let uu____5303 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____5303
             else ());
            (let uu____5305 = FStar_Options.use_two_phase_tc () in
             if uu____5305
             then
               let uu____5312 =
                 check_top_level_let
                   (let uu___345_5321 = env1 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___345_5321.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___345_5321.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___345_5321.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___345_5321.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___345_5321.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___345_5321.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___345_5321.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___345_5321.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___345_5321.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___345_5321.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___345_5321.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___345_5321.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___345_5321.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___345_5321.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___345_5321.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___345_5321.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___345_5321.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___345_5321.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___345_5321.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___345_5321.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___345_5321.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___345_5321.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___345_5321.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___345_5321.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___345_5321.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___345_5321.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___345_5321.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___345_5321.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___345_5321.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___345_5321.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___345_5321.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___345_5321.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___345_5321.FStar_TypeChecker_Env.dep_graph)
                    }) top in
               match uu____5312 with
               | (lax_top,l,g) ->
                   let lax_top1 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       lax_top in
                   ((let uu____5333 =
                       FStar_Syntax_Print.term_to_string lax_top1 in
                     FStar_Util.print1 "Phase 1: checked %s\n" uu____5333);
                    (let uu____5334 =
                       FStar_TypeChecker_Env.should_verify env1 in
                     if uu____5334
                     then check_top_level_let env1 lax_top1
                     else (lax_top1, l, g)))
             else check_top_level_let env1 top))
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____5343),uu____5344) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5359;
                FStar_Syntax_Syntax.lbunivs = uu____5360;
                FStar_Syntax_Syntax.lbtyp = uu____5361;
                FStar_Syntax_Syntax.lbeff = uu____5362;
                FStar_Syntax_Syntax.lbdef = uu____5363;_}::uu____5364),uu____5365)
           ->
           ((let uu____5387 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5387
             then
               let uu____5388 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____5388
             else ());
            (let uu____5390 = FStar_Options.use_two_phase_tc () in
             if uu____5390
             then
               let uu____5397 =
                 check_top_level_let_rec
                   (let uu___346_5406 = env1 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___346_5406.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___346_5406.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___346_5406.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___346_5406.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___346_5406.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___346_5406.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___346_5406.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___346_5406.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___346_5406.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___346_5406.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___346_5406.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___346_5406.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___346_5406.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___346_5406.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___346_5406.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___346_5406.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___346_5406.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___346_5406.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___346_5406.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___346_5406.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___346_5406.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___346_5406.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___346_5406.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___346_5406.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___346_5406.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___346_5406.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___346_5406.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___346_5406.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___346_5406.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___346_5406.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___346_5406.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___346_5406.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___346_5406.FStar_TypeChecker_Env.dep_graph)
                    }) top in
               match uu____5397 with
               | (lax_top,l,g) ->
                   let lax_top1 =
                     FStar_TypeChecker_Normalize.remove_uvar_solutions env1
                       lax_top in
                   ((let uu____5418 =
                       FStar_Syntax_Print.term_to_string lax_top1 in
                     FStar_Util.print1 "Phase 1: checked %s\n" uu____5418);
                    (let uu____5419 =
                       FStar_TypeChecker_Env.should_verify env1 in
                     if uu____5419
                     then check_top_level_let_rec env1 lax_top1
                     else (lax_top1, l, g)))
             else check_top_level_let_rec env1 top))
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____5428),uu____5429) ->
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
        let uu____5455 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5545))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5605))::(uu____5606,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____5607))::
              (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____5680 ->
              FStar_Exn.raise
                (FStar_Errors.Error ("synth_by_tactic: bad application", rng)) in
        match uu____5455 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____5764 = FStar_TypeChecker_Env.expected_typ env in
                  (match uu____5764 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____5770 =
                         let uu____5771 =
                           let uu____5776 =
                             FStar_TypeChecker_Env.get_range env in
                           ("synth_by_tactic: need a type annotation when no expected type is present",
                             uu____5776) in
                         FStar_Errors.Error uu____5771 in
                       FStar_Exn.raise uu____5770) in
            let uu____5779 = FStar_TypeChecker_Env.clear_expected_typ env in
            (match uu____5779 with
             | (env',uu____5793) ->
                 let uu____5798 = tc_term env' typ in
                 (match uu____5798 with
                  | (typ1,uu____5812,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____5815 = tc_tactic env' tau in
                        match uu____5815 with
                        | (tau1,uu____5829,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let t =
                                if env.FStar_TypeChecker_Env.nosynth
                                then
                                  let uu____5837 =
                                    let uu____5838 =
                                      FStar_TypeChecker_Util.fvar_const env
                                        FStar_Parser_Const.magic_lid in
                                    let uu____5839 =
                                      let uu____5840 =
                                        FStar_Syntax_Syntax.as_arg
                                          FStar_Syntax_Util.exp_unit in
                                      [uu____5840] in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____5838
                                      uu____5839 in
                                  uu____5837 FStar_Pervasives_Native.None rng
                                else
                                  (let t =
                                     env.FStar_TypeChecker_Env.synth env'
                                       typ1 tau1 in
                                   (let uu____5846 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Tac") in
                                    if uu____5846
                                    then
                                      let uu____5847 =
                                        FStar_Syntax_Print.term_to_string t in
                                      FStar_Util.print1 "Got %s\n" uu____5847
                                    else ());
                                   t) in
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____5850 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng in
                               tc_term env uu____5850)))))))
and tc_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___347_5854 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___347_5854.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___347_5854.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___347_5854.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___347_5854.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___347_5854.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___347_5854.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___347_5854.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___347_5854.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___347_5854.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___347_5854.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___347_5854.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___347_5854.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___347_5854.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___347_5854.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___347_5854.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___347_5854.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___347_5854.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___347_5854.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___347_5854.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___347_5854.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___347_5854.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___347_5854.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___347_5854.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___347_5854.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___347_5854.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___347_5854.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___347_5854.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___347_5854.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___347_5854.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___347_5854.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___347_5854.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___347_5854.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___347_5854.FStar_TypeChecker_Env.dep_graph)
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
        let uu___348_5858 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___348_5858.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___348_5858.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___348_5858.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___348_5858.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___348_5858.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___348_5858.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___348_5858.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___348_5858.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___348_5858.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___348_5858.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___348_5858.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___348_5858.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___348_5858.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___348_5858.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___348_5858.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___348_5858.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___348_5858.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___348_5858.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___348_5858.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___348_5858.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___348_5858.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___348_5858.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___348_5858.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___348_5858.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___348_5858.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___348_5858.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___348_5858.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___348_5858.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___348_5858.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___348_5858.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___348_5858.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___348_5858.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___348_5858.FStar_TypeChecker_Env.dep_graph)
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
          let uu____5874 = tc_tactic env tactic in
          (match uu____5874 with
           | (tactic1,uu____5884,uu____5885) ->
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
        let uu____5924 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____5924 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____5945 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____5945
              then FStar_Util.Inl t1
              else
                (let uu____5951 =
                   let uu____5952 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____5952 in
                 FStar_Util.Inr uu____5951) in
            let is_data_ctor uu___333_5962 =
              match uu___333_5962 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____5965) -> true
              | uu____5972 -> false in
            let uu____5975 =
              (is_data_ctor dc) &&
                (let uu____5977 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____5977) in
            if uu____5975
            then
              let uu____5984 =
                let uu____5985 =
                  let uu____5990 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____5991 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____5990, uu____5991) in
                FStar_Errors.Error uu____5985 in
              FStar_Exn.raise uu____5984
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____6008 =
            let uu____6009 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____6009 in
          failwith uu____6008
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____6043 =
              let uu____6044 = FStar_Syntax_Subst.compress t1 in
              uu____6044.FStar_Syntax_Syntax.n in
            match uu____6043 with
            | FStar_Syntax_Syntax.Tm_arrow uu____6047 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____6060 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___349_6098 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___349_6098.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___349_6098.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___349_6098.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____6150 =
            let uu____6163 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____6163 with
            | FStar_Pervasives_Native.None  ->
                let uu____6178 = FStar_Syntax_Util.type_u () in
                (match uu____6178 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____6150 with
           | (t,uu____6215,g0) ->
               let uu____6229 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____6229 with
                | (e1,uu____6249,g1) ->
                    let uu____6263 =
                      let uu____6264 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____6264
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____6265 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____6263, uu____6265)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____6267 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____6280 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____6280)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____6267 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___350_6299 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___350_6299.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___350_6299.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____6302 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____6302 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____6323 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____6323
                       then FStar_Util.Inl t1
                       else
                         (let uu____6329 =
                            let uu____6330 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____6330 in
                          FStar_Util.Inr uu____6329) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6336;
             FStar_Syntax_Syntax.vars = uu____6337;_},uu____6338)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____6343 =
            let uu____6344 =
              let uu____6349 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____6349) in
            FStar_Errors.Error uu____6344 in
          FStar_Exn.raise uu____6343
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____6357 =
            let uu____6358 =
              let uu____6363 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____6363) in
            FStar_Errors.Error uu____6358 in
          FStar_Exn.raise uu____6357
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6371;
             FStar_Syntax_Syntax.vars = uu____6372;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____6381 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6381 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____6404 =
                     let uu____6405 =
                       let uu____6410 =
                         let uu____6411 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____6412 =
                           FStar_Util.string_of_int (FStar_List.length us1) in
                         let uu____6413 =
                           FStar_Util.string_of_int (FStar_List.length us') in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____6411 uu____6412 uu____6413 in
                       let uu____6414 = FStar_TypeChecker_Env.get_range env1 in
                       (uu____6410, uu____6414) in
                     FStar_Errors.Error uu____6405 in
                   FStar_Exn.raise uu____6404)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____6430 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6434 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6434 us1 in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6436 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6436 with
           | ((us,t),range) ->
               ((let uu____6459 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____6459
                 then
                   let uu____6460 =
                     let uu____6461 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____6461 in
                   let uu____6462 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____6463 = FStar_Range.string_of_range range in
                   let uu____6464 = FStar_Range.string_of_use_range range in
                   let uu____6465 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____6460 uu____6462 uu____6463 uu____6464 uu____6465
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6470 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6470 us in
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
          let uu____6494 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6494 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____6508 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____6508 with
                | (env2,uu____6522) ->
                    let uu____6527 = tc_binders env2 bs1 in
                    (match uu____6527 with
                     | (bs2,env3,g,us) ->
                         let uu____6546 = tc_comp env3 c1 in
                         (match uu____6546 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___351_6565 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___351_6565.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___351_6565.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____6574 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____6574 in
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
          let uu____6593 =
            let uu____6598 =
              let uu____6599 = FStar_Syntax_Syntax.mk_binder x in
              [uu____6599] in
            FStar_Syntax_Subst.open_term uu____6598 phi in
          (match uu____6593 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____6609 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____6609 with
                | (env2,uu____6623) ->
                    let uu____6628 =
                      let uu____6641 = FStar_List.hd x1 in
                      tc_binder env2 uu____6641 in
                    (match uu____6628 with
                     | (x2,env3,f1,u) ->
                         ((let uu____6669 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____6669
                           then
                             let uu____6670 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____6671 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____6672 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____6670 uu____6671 uu____6672
                           else ());
                          (let uu____6674 = FStar_Syntax_Util.type_u () in
                           match uu____6674 with
                           | (t_phi,uu____6686) ->
                               let uu____6687 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____6687 with
                                | (phi2,uu____6701,f2) ->
                                    let e1 =
                                      let uu___352_6706 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___352_6706.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___352_6706.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____6713 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____6713 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____6726) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____6749 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____6749
            then
              let uu____6750 =
                FStar_Syntax_Print.term_to_string
                  (let uu___353_6753 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___353_6753.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___353_6753.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____6750
            else ());
           (let uu____6759 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____6759 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____6772 ->
          let uu____6773 =
            let uu____6774 = FStar_Syntax_Print.term_to_string top in
            let uu____6775 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____6774
              uu____6775 in
          failwith uu____6773
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
      | FStar_Const.Const_bool uu____6784 -> FStar_Syntax_Util.t_bool
      | FStar_Const.Const_int (uu____6785,FStar_Pervasives_Native.None ) ->
          FStar_Syntax_Syntax.t_int
      | FStar_Const.Const_int
          (uu____6796,FStar_Pervasives_Native.Some uu____6797) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____6812 -> FStar_Syntax_Syntax.t_string
      | FStar_Const.Const_float uu____6817 -> FStar_Syntax_Syntax.t_float
      | FStar_Const.Const_char uu____6818 -> FStar_Syntax_Syntax.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____6819 -> FStar_Syntax_Syntax.t_range
      | FStar_Const.Const_range_of  ->
          let uu____6820 =
            let uu____6821 =
              let uu____6826 =
                let uu____6827 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6827 in
              (uu____6826, r) in
            FStar_Errors.Error uu____6821 in
          FStar_Exn.raise uu____6820
      | FStar_Const.Const_set_range_of  ->
          let uu____6828 =
            let uu____6829 =
              let uu____6834 =
                let uu____6835 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6835 in
              (uu____6834, r) in
            FStar_Errors.Error uu____6829 in
          FStar_Exn.raise uu____6828
      | FStar_Const.Const_reify  ->
          let uu____6836 =
            let uu____6837 =
              let uu____6842 =
                let uu____6843 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6843 in
              (uu____6842, r) in
            FStar_Errors.Error uu____6837 in
          FStar_Exn.raise uu____6836
      | FStar_Const.Const_reflect uu____6844 ->
          let uu____6845 =
            let uu____6846 =
              let uu____6851 =
                let uu____6852 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6852 in
              (uu____6851, r) in
            FStar_Errors.Error uu____6846 in
          FStar_Exn.raise uu____6845
      | uu____6853 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____6870) ->
          let uu____6879 = FStar_Syntax_Util.type_u () in
          (match uu____6879 with
           | (k,u) ->
               let uu____6892 = tc_check_tot_or_gtot_term env t k in
               (match uu____6892 with
                | (t1,uu____6906,g) ->
                    let uu____6908 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____6908, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____6910) ->
          let uu____6919 = FStar_Syntax_Util.type_u () in
          (match uu____6919 with
           | (k,u) ->
               let uu____6932 = tc_check_tot_or_gtot_term env t k in
               (match uu____6932 with
                | (t1,uu____6946,g) ->
                    let uu____6948 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____6948, u, g)))
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
            let uu____6956 =
              let uu____6957 =
                let uu____6958 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____6958 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____6957 in
            uu____6956 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____6961 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____6961 with
           | (tc1,uu____6975,f) ->
               let uu____6977 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____6977 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____7021 =
                        let uu____7022 = FStar_Syntax_Subst.compress head3 in
                        uu____7022.FStar_Syntax_Syntax.n in
                      match uu____7021 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____7025,us) -> us
                      | uu____7031 -> [] in
                    let uu____7032 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____7032 with
                     | (uu____7053,args1) ->
                         let uu____7075 =
                           let uu____7094 = FStar_List.hd args1 in
                           let uu____7107 = FStar_List.tl args1 in
                           (uu____7094, uu____7107) in
                         (match uu____7075 with
                          | (res,args2) ->
                              let uu____7172 =
                                let uu____7181 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___334_7209  ->
                                          match uu___334_7209 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____7217 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____7217 with
                                               | (env1,uu____7229) ->
                                                   let uu____7234 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____7234 with
                                                    | (e1,uu____7246,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____7181
                                  FStar_List.unzip in
                              (match uu____7172 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___354_7285 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___354_7285.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___354_7285.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____7289 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____7289 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____7293 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____7293))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____7301 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____7302 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____7312 = aux u3 in FStar_Syntax_Syntax.U_succ uu____7312
        | FStar_Syntax_Syntax.U_max us ->
            let uu____7316 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____7316
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____7321 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____7321 FStar_Pervasives_Native.snd
         | uu____7330 -> aux u)
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
            let uu____7354 =
              let uu____7355 =
                let uu____7360 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____7360, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____7355 in
            FStar_Exn.raise uu____7354 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____7450 bs2 bs_expected1 =
              match uu____7450 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____7618)) ->
                             let uu____7623 =
                               let uu____7624 =
                                 let uu____7629 =
                                   let uu____7630 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____7630 in
                                 let uu____7631 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____7629, uu____7631) in
                               FStar_Errors.Error uu____7624 in
                             FStar_Exn.raise uu____7623
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____7632),FStar_Pervasives_Native.None ) ->
                             let uu____7637 =
                               let uu____7638 =
                                 let uu____7643 =
                                   let uu____7644 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____7644 in
                                 let uu____7645 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____7643, uu____7645) in
                               FStar_Errors.Error uu____7638 in
                             FStar_Exn.raise uu____7637
                         | uu____7646 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____7652 =
                           let uu____7657 =
                             let uu____7658 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____7658.FStar_Syntax_Syntax.n in
                           match uu____7657 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____7665 ->
                               ((let uu____7667 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____7667
                                 then
                                   let uu____7668 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____7668
                                 else ());
                                (let uu____7670 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____7670 with
                                 | (t,uu____7682,g1) ->
                                     let g2 =
                                       let uu____7685 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____7686 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____7685
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____7686 in
                                     let g3 =
                                       let uu____7688 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____7688 in
                                     (t, g3))) in
                         match uu____7652 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___355_7716 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___355_7716.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___355_7716.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____7729 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____7729 in
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
                  | uu____7877 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____7886 = tc_binders env1 bs in
                  match uu____7886 with
                  | (bs1,envbody,g,uu____7916) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____7960 =
                    let uu____7961 = FStar_Syntax_Subst.compress t2 in
                    uu____7961.FStar_Syntax_Syntax.n in
                  match uu____7960 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____7984 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8008 -> failwith "Impossible");
                       (let uu____8017 = tc_binders env1 bs in
                        match uu____8017 with
                        | (bs1,envbody,g,uu____8049) ->
                            let uu____8050 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____8050 with
                             | (envbody1,uu____8078) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____8089;
                         FStar_Syntax_Syntax.pos = uu____8090;
                         FStar_Syntax_Syntax.vars = uu____8091;_},uu____8092)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8136 -> failwith "Impossible");
                       (let uu____8145 = tc_binders env1 bs in
                        match uu____8145 with
                        | (bs1,envbody,g,uu____8177) ->
                            let uu____8178 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____8178 with
                             | (envbody1,uu____8206) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____8218) ->
                      let uu____8223 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____8223 with
                       | (uu____8264,bs1,bs',copt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____8307 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____8307 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____8407 c_expected2 =
                               match uu____8407 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____8522 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____8522)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____8553 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____8553 in
                                        let uu____8554 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____8554)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        let uu____8579 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c) in
                                        if uu____8579
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
                                               let uu____8627 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____8627 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____8648 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____8648 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____8696 =
                                                           let uu____8727 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____8727,
                                                             subst2) in
                                                         handle_more
                                                           uu____8696
                                                           c_expected4))
                                           | uu____8744 ->
                                               let uu____8745 =
                                                 let uu____8746 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____8746 in
                                               fail uu____8745 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____8776 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____8776 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___356_8837 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___356_8837.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___356_8837.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___356_8837.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___356_8837.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___356_8837.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___356_8837.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___356_8837.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___356_8837.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___356_8837.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___356_8837.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___356_8837.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___356_8837.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___356_8837.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___356_8837.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___356_8837.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___356_8837.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___356_8837.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___356_8837.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___356_8837.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___356_8837.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___356_8837.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___356_8837.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___356_8837.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___356_8837.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___356_8837.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___356_8837.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___356_8837.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___356_8837.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___356_8837.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___356_8837.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___356_8837.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___356_8837.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___356_8837.FStar_TypeChecker_Env.dep_graph)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____8885  ->
                                     fun uu____8886  ->
                                       match (uu____8885, uu____8886) with
                                       | ((env2,letrec_binders),(l,t3,u_names))
                                           ->
                                           let uu____8948 =
                                             let uu____8955 =
                                               let uu____8956 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____8956
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____8955 t3 in
                                           (match uu____8948 with
                                            | (t4,uu____8978,uu____8979) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (u_names, t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____8989 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___357_8992
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___357_8992.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___357_8992.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____8989 ::
                                                        letrec_binders
                                                  | uu____8993 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____8998 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____8998 with
                            | (envbody,bs1,g,c) ->
                                let uu____9049 =
                                  let uu____9056 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____9056
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____9049 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body1, g))))
                  | uu____9105 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____9126 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____9126
                      else
                        (let uu____9128 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1 in
                         match uu____9128 with
                         | (uu____9167,bs1,uu____9169,c_opt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____9189 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____9189 with
          | (env1,topt) ->
              ((let uu____9209 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____9209
                then
                  let uu____9210 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____9210
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____9214 = expected_function_typ1 env1 topt body in
                match uu____9214 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let uu____9254 =
                      let should_check_expected_effect =
                        let uu____9262 =
                          let uu____9269 =
                            let uu____9270 =
                              FStar_Syntax_Subst.compress body1 in
                            uu____9270.FStar_Syntax_Syntax.n in
                          (c_opt, uu____9269) in
                        match uu____9262 with
                        | (FStar_Pervasives_Native.None
                           ,FStar_Syntax_Syntax.Tm_ascribed
                           (uu____9275,(FStar_Util.Inr expected_c,uu____9277),uu____9278))
                            -> false
                        | uu____9327 -> true in
                      let uu____9334 =
                        tc_term
                          (let uu___358_9343 = envbody in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___358_9343.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___358_9343.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___358_9343.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___358_9343.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___358_9343.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___358_9343.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___358_9343.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___358_9343.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___358_9343.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___358_9343.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___358_9343.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___358_9343.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___358_9343.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = false;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___358_9343.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq = use_eq;
                             FStar_TypeChecker_Env.is_iface =
                               (uu___358_9343.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___358_9343.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___358_9343.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___358_9343.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___358_9343.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___358_9343.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___358_9343.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___358_9343.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___358_9343.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___358_9343.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qname_and_index =
                               (uu___358_9343.FStar_TypeChecker_Env.qname_and_index);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___358_9343.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth =
                               (uu___358_9343.FStar_TypeChecker_Env.synth);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___358_9343.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___358_9343.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___358_9343.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___358_9343.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___358_9343.FStar_TypeChecker_Env.dep_graph)
                           }) body1 in
                      match uu____9334 with
                      | (body2,cbody,guard_body) ->
                          let guard_body1 =
                            FStar_TypeChecker_Rel.solve_deferred_constraints
                              envbody guard_body in
                          if should_check_expected_effect
                          then
                            let uu____9360 =
                              let uu____9367 =
                                let uu____9372 =
                                  cbody.FStar_Syntax_Syntax.comp () in
                                (body2, uu____9372) in
                              check_expected_effect
                                (let uu___359_9379 = envbody in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___359_9379.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___359_9379.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___359_9379.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___359_9379.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___359_9379.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___359_9379.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___359_9379.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___359_9379.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___359_9379.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___359_9379.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___359_9379.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___359_9379.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___359_9379.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___359_9379.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___359_9379.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___359_9379.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___359_9379.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___359_9379.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___359_9379.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___359_9379.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___359_9379.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___359_9379.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___359_9379.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___359_9379.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___359_9379.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___359_9379.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___359_9379.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___359_9379.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___359_9379.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___359_9379.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___359_9379.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___359_9379.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___359_9379.FStar_TypeChecker_Env.dep_graph)
                                 }) c_opt uu____9367 in
                            (match uu____9360 with
                             | (body3,cbody1,guard) ->
                                 let uu____9389 =
                                   FStar_TypeChecker_Rel.conj_guard
                                     guard_body1 guard in
                                 (body3, cbody1, uu____9389))
                          else
                            (let uu____9391 =
                               cbody.FStar_Syntax_Syntax.comp () in
                             (body2, uu____9391, guard_body1)) in
                    (match uu____9254 with
                     | (body2,cbody,guard) ->
                         let guard1 =
                           let uu____9406 =
                             env1.FStar_TypeChecker_Env.top_level ||
                               (let uu____9408 =
                                  FStar_TypeChecker_Env.should_verify env1 in
                                Prims.op_Negation uu____9408) in
                           if uu____9406
                           then
                             let uu____9409 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             FStar_TypeChecker_Rel.discharge_guard envbody
                               uu____9409
                           else
                             (let guard1 =
                                let uu____9412 =
                                  FStar_TypeChecker_Rel.conj_guard g guard in
                                FStar_TypeChecker_Rel.close_guard env1
                                  (FStar_List.append bs1 letrec_binders)
                                  uu____9412 in
                              guard1) in
                         let tfun_computed =
                           FStar_Syntax_Util.arrow bs1 cbody in
                         let e =
                           FStar_Syntax_Util.abs bs1 body2
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp
                                   (FStar_Util.dflt cbody c_opt))) in
                         let uu____9421 =
                           match tfun_opt with
                           | FStar_Pervasives_Native.Some t ->
                               let t1 = FStar_Syntax_Subst.compress t in
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_arrow uu____9442 ->
                                    (e, t1, guard1)
                                | uu____9455 ->
                                    let uu____9456 =
                                      FStar_TypeChecker_Util.check_and_ascribe
                                        env1 e tfun_computed t1 in
                                    (match uu____9456 with
                                     | (e1,guard') ->
                                         let uu____9469 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 guard' in
                                         (e1, t1, uu____9469)))
                           | FStar_Pervasives_Native.None  ->
                               (e, tfun_computed, guard1) in
                         (match uu____9421 with
                          | (e1,tfun,guard2) ->
                              let c =
                                if env1.FStar_TypeChecker_Env.top_level
                                then FStar_Syntax_Syntax.mk_Total tfun
                                else
                                  FStar_TypeChecker_Util.return_value env1
                                    tfun e1 in
                              let uu____9483 =
                                FStar_TypeChecker_Util.strengthen_precondition
                                  FStar_Pervasives_Native.None env1 e1
                                  (FStar_Syntax_Util.lcomp_of_comp c) guard2 in
                              (match uu____9483 with
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
              (let uu____9532 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____9532
               then
                 let uu____9533 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____9534 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____9533
                   uu____9534
               else ());
              (let monadic_application uu____9591 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____9591 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___360_9650 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___360_9650.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___360_9650.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___360_9650.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____9651 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
                       | uu____9666 ->
                           let g =
                             let uu____9674 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____9674
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____9675 =
                             let uu____9676 =
                               let uu____9679 =
                                 let uu____9680 =
                                   let uu____9681 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____9681 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____9680 in
                               FStar_Syntax_Syntax.mk_Total uu____9679 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____9676 in
                           (uu____9675, g) in
                     (match uu____9651 with
                      | (cres2,guard1) ->
                          ((let uu____9695 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____9695
                            then
                              let uu____9696 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____9696
                            else ());
                           (let cres3 =
                              let uu____9699 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____9699
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
                                   fun uu____9733  ->
                                     match uu____9733 with
                                     | ((e,q),x,c) ->
                                         let uu____9766 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____9766
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
                              let uu____9778 =
                                let uu____9779 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____9779.FStar_Syntax_Syntax.n in
                              match uu____9778 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____9783 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____9804  ->
                                         match uu____9804 with
                                         | (arg,uu____9818,uu____9819) -> arg
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
                                (let uu____9829 =
                                   let map_fun uu____9891 =
                                     match uu____9891 with
                                     | ((e,q),uu____9926,c) ->
                                         let uu____9936 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____9936
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
                                            let uu____9986 =
                                              let uu____9991 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____9991, q) in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____9986)) in
                                   let uu____10020 =
                                     let uu____10045 =
                                       let uu____10068 =
                                         let uu____10083 =
                                           let uu____10092 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____10092,
                                             FStar_Pervasives_Native.None,
                                             chead1) in
                                         uu____10083 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____10068 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____10045 in
                                   match uu____10020 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____10265 =
                                         let uu____10266 =
                                           FStar_List.hd reverse_args in
                                         FStar_Pervasives_Native.fst
                                           uu____10266 in
                                       let uu____10275 =
                                         let uu____10282 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____10282 in
                                       (lifted_args, uu____10265,
                                         uu____10275) in
                                 match uu____9829 with
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
                                     let bind_lifted_args e uu___335_10385 =
                                       match uu___335_10385 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____10440 =
                                               let uu____10443 =
                                                 let uu____10444 =
                                                   let uu____10457 =
                                                     let uu____10458 =
                                                       let uu____10459 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____10459] in
                                                     FStar_Syntax_Subst.close
                                                       uu____10458 e in
                                                   ((false, [lb]),
                                                     uu____10457) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____10444 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10443 in
                                             uu____10440
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
                            let uu____10489 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp1
                                guard1 in
                            match uu____10489 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____10580 bs args1 =
                 match uu____10580 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____10727))::rest,
                         (uu____10729,FStar_Pervasives_Native.None )::uu____10730)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t in
                          let uu____10791 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____10791 with
                           | (varg,uu____10811,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____10833 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____10833) in
                               let uu____10834 =
                                 let uu____10869 =
                                   let uu____10884 =
                                     let uu____10897 =
                                       let uu____10898 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____10898
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____10897) in
                                   uu____10884 :: outargs in
                                 let uu____10917 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____10869, (arg :: arg_rets),
                                   uu____10917, fvs) in
                               tc_args head_info uu____10834 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____11019),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11020)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____11033 ->
                                FStar_Exn.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___361_11044 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___361_11044.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___361_11044.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____11046 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____11046
                             then
                               let uu____11047 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____11047
                             else ());
                            (let targ1 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___362_11052 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___362_11052.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___362_11052.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___362_11052.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___362_11052.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___362_11052.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___362_11052.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___362_11052.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___362_11052.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___362_11052.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___362_11052.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___362_11052.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___362_11052.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___362_11052.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___362_11052.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___362_11052.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___362_11052.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___362_11052.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___362_11052.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___362_11052.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___362_11052.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___362_11052.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___362_11052.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___362_11052.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___362_11052.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___362_11052.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___362_11052.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___362_11052.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___362_11052.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___362_11052.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___362_11052.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___362_11052.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___362_11052.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___362_11052.FStar_TypeChecker_Env.dep_graph)
                               } in
                             (let uu____11054 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____11054
                              then
                                let uu____11055 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____11056 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11057 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____11055 uu____11056 uu____11057
                              else ());
                             (let uu____11059 = tc_term env2 e in
                              match uu____11059 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____11086 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____11086 in
                                  let uu____11087 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____11087
                                  then
                                    let subst2 =
                                      let uu____11095 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____11095
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
                      | (uu____11189,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____11225) ->
                          let uu____11276 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____11276 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____11310 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____11310
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____11335 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____11335 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____11358 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____11358
                                            then
                                              FStar_Errors.warn
                                                tres1.FStar_Syntax_Syntax.pos
                                                "Potentially redundant explicit currying of a function type"
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____11400 when Prims.op_Negation norm1
                                     ->
                                     let uu____11401 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____11401
                                 | uu____11402 ->
                                     let uu____11403 =
                                       let uu____11404 =
                                         let uu____11409 =
                                           let uu____11410 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____11411 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____11410 uu____11411 in
                                         let uu____11418 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____11409, uu____11418) in
                                       FStar_Errors.Error uu____11404 in
                                     FStar_Exn.raise uu____11403 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____11437 =
                   let uu____11438 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____11438.FStar_Syntax_Syntax.n in
                 match uu____11437 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____11449 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____11550 = tc_term env1 e in
                           (match uu____11550 with
                            | (e1,c,g_e) ->
                                let uu____11572 = tc_args1 env1 tl1 in
                                (match uu____11572 with
                                 | (args2,comps,g_rest) ->
                                     let uu____11612 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____11612))) in
                     let uu____11633 = tc_args1 env args in
                     (match uu____11633 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____11670 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____11708  ->
                                      match uu____11708 with
                                      | (uu____11721,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____11670 in
                          let ml_or_tot t r1 =
                            let uu____11738 = FStar_Options.ml_ish () in
                            if uu____11738
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____11741 =
                              let uu____11744 =
                                let uu____11745 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____11745
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____11744 in
                            ml_or_tot uu____11741 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____11758 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____11758
                            then
                              let uu____11759 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____11760 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____11761 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____11759 uu____11760 uu____11761
                            else ());
                           (let uu____11764 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____11764);
                           (let comp =
                              let uu____11766 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____11777  ->
                                   fun out  ->
                                     match uu____11777 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____11766 in
                            let uu____11791 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____11794 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____11791, comp, uu____11794))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____11797;
                        FStar_Syntax_Syntax.pos = uu____11798;
                        FStar_Syntax_Syntax.vars = uu____11799;_},uu____11800)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____11921 = tc_term env1 e in
                           (match uu____11921 with
                            | (e1,c,g_e) ->
                                let uu____11943 = tc_args1 env1 tl1 in
                                (match uu____11943 with
                                 | (args2,comps,g_rest) ->
                                     let uu____11983 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____11983))) in
                     let uu____12004 = tc_args1 env args in
                     (match uu____12004 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____12041 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____12079  ->
                                      match uu____12079 with
                                      | (uu____12092,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____12041 in
                          let ml_or_tot t r1 =
                            let uu____12109 = FStar_Options.ml_ish () in
                            if uu____12109
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____12112 =
                              let uu____12115 =
                                let uu____12116 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____12116
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____12115 in
                            ml_or_tot uu____12112 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____12129 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____12129
                            then
                              let uu____12130 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____12131 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____12132 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____12130 uu____12131 uu____12132
                            else ());
                           (let uu____12135 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____12135);
                           (let comp =
                              let uu____12137 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____12148  ->
                                   fun out  ->
                                     match uu____12148 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____12137 in
                            let uu____12162 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____12165 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____12162, comp, uu____12165))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____12186 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____12186 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____12251) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____12257,uu____12258) -> check_function_app t
                 | uu____12299 ->
                     let uu____12300 =
                       let uu____12301 =
                         let uu____12306 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____12306, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____12301 in
                     FStar_Exn.raise uu____12300 in
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
                  let uu____12376 =
                    FStar_List.fold_left2
                      (fun uu____12419  ->
                         fun uu____12420  ->
                           fun uu____12421  ->
                             match (uu____12419, uu____12420, uu____12421)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Exn.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____12489 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____12489 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____12507 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____12507 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____12511 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____12511)
                                              &&
                                              (let uu____12513 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____12513)) in
                                       let uu____12514 =
                                         let uu____12523 =
                                           let uu____12532 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____12532] in
                                         FStar_List.append seen uu____12523 in
                                       let uu____12539 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____12514, uu____12539, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____12376 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r in
                       let c1 =
                         if ghost
                         then
                           let uu____12575 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____12575
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____12577 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____12577 with | (c2,g) -> (e, c2, g)))
              | uu____12594 ->
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
        let uu____12628 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____12628 with
        | (pattern,when_clause,branch_exp) ->
            let uu____12664 = branch1 in
            (match uu____12664 with
             | (cpat,uu____12696,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let tc_annot env1 t =
                     let uu____12755 = FStar_Syntax_Util.type_u () in
                     match uu____12755 with
                     | (tu,u) ->
                         let uu____12762 =
                           tc_check_tot_or_gtot_term env1 t tu in
                         (match uu____12762 with
                          | (t1,uu____12770,g) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env1
                                 g;
                               t1)) in
                   let uu____12773 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0
                       tc_annot in
                   match uu____12773 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____12802 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____12802
                         then
                           let uu____12803 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____12804 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____12803 uu____12804
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____12807 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____12807 with
                         | (env1,uu____12827) ->
                             let env11 =
                               let uu___363_12833 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___363_12833.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___363_12833.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___363_12833.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___363_12833.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___363_12833.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___363_12833.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___363_12833.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___363_12833.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___363_12833.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___363_12833.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___363_12833.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___363_12833.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___363_12833.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___363_12833.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___363_12833.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___363_12833.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___363_12833.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___363_12833.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___363_12833.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___363_12833.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___363_12833.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___363_12833.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___363_12833.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___363_12833.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___363_12833.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___363_12833.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___363_12833.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___363_12833.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___363_12833.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___363_12833.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___363_12833.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___363_12833.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___363_12833.FStar_TypeChecker_Env.dep_graph)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____12836 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____12836
                               then
                                 let uu____12837 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____12838 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____12837 uu____12838
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t in
                               let uu____12841 =
                                 tc_tot_or_gtot_term env12 exp in
                               match uu____12841 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___364_12864 = g in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___364_12864.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___364_12864.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___364_12864.FStar_TypeChecker_Env.implicits)
                                     } in
                                   let uu____12865 =
                                     let uu____12866 =
                                       FStar_TypeChecker_Rel.teq_nosmt env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t in
                                     if uu____12866
                                     then
                                       let env13 =
                                         FStar_TypeChecker_Env.set_range
                                           env12 exp1.FStar_Syntax_Syntax.pos in
                                       let uu____12868 =
                                         FStar_TypeChecker_Rel.discharge_guard_no_smt
                                           env13 g1 in
                                       FStar_All.pipe_right uu____12868
                                         FStar_TypeChecker_Rel.resolve_implicits
                                     else
                                       (let uu____12870 =
                                          let uu____12871 =
                                            let uu____12876 =
                                              let uu____12877 =
                                                FStar_Syntax_Print.term_to_string
                                                  lc.FStar_Syntax_Syntax.res_typ in
                                              let uu____12878 =
                                                FStar_Syntax_Print.term_to_string
                                                  expected_pat_t in
                                              FStar_Util.format2
                                                "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                                uu____12877 uu____12878 in
                                            (uu____12876,
                                              (exp1.FStar_Syntax_Syntax.pos)) in
                                          FStar_Errors.Error uu____12871 in
                                        FStar_Exn.raise uu____12870) in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1 in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____12895 =
                                       let uu____12896 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____12896 in
                                     if uu____12895
                                     then
                                       let unresolved =
                                         let uu____12908 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____12908
                                           FStar_Util.set_elements in
                                       let uu____12935 =
                                         let uu____12936 =
                                           let uu____12941 =
                                             let uu____12942 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____12943 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____12944 =
                                               let uu____12945 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____12963  ->
                                                         match uu____12963
                                                         with
                                                         | (u,uu____12969) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____12945
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____12942 uu____12943
                                               uu____12944 in
                                           (uu____12941,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____12936 in
                                       FStar_Exn.raise uu____12935
                                     else ());
                                    (let uu____12974 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____12974
                                     then
                                       let uu____12975 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____12975
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____12984 =
                   let uu____12991 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____12991
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____12984 with
                  | (scrutinee_env,uu____13015) ->
                      let uu____13020 = tc_pat true pat_t pattern in
                      (match uu____13020 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____13058 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____13080 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____13080
                                 then
                                   FStar_Exn.raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____13094 =
                                      let uu____13101 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool in
                                      tc_term uu____13101 e in
                                    match uu____13094 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g)) in
                           (match uu____13058 with
                            | (when_clause1,g_when) ->
                                let uu____13135 = tc_term pat_env branch_exp in
                                (match uu____13135 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some w ->
                                           let uu____13167 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_41  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_41) uu____13167 in
                                     let uu____13170 =
                                       let eqs =
                                         let uu____13180 =
                                           let uu____13181 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____13181 in
                                         if uu____13180
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____13188 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____13205 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____13206 ->
                                                FStar_Pervasives_Native.None
                                            | uu____13207 ->
                                                let uu____13208 =
                                                  let uu____13209 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____13209 pat_t
                                                    scrutinee_tm e in
                                                FStar_Pervasives_Native.Some
                                                  uu____13208) in
                                       let uu____13210 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch in
                                       match uu____13210 with
                                       | (c1,g_branch1) ->
                                           let uu____13225 =
                                             match (eqs, when_condition) with
                                             | uu____13238 when
                                                 let uu____13247 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation
                                                   uu____13247
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
                                                 let uu____13259 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____13260 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____13259, uu____13260)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____13269 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____13269 in
                                                 let uu____13270 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____13271 =
                                                   let uu____13272 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____13272 g_when in
                                                 (uu____13270, uu____13271)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____13280 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____13280, g_when) in
                                           (match uu____13225 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____13292 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____13293 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____13292, uu____13293,
                                                  g_branch1)) in
                                     (match uu____13170 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____13314 =
                                              let uu____13315 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____13315 in
                                            if uu____13314
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____13345 =
                                                     let uu____13346 =
                                                       let uu____13347 =
                                                         let uu____13350 =
                                                           let uu____13357 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____13357 in
                                                         FStar_Pervasives_Native.snd
                                                           uu____13350 in
                                                       FStar_List.length
                                                         uu____13347 in
                                                     uu____13346 >
                                                       (Prims.parse_int "1") in
                                                   if uu____13345
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____13363 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____13363 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____13384 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None in
                                                         let disc1 =
                                                           let uu____13399 =
                                                             let uu____13400
                                                               =
                                                               let uu____13401
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____13401] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____13400 in
                                                           uu____13399
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____13404 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool in
                                                         [uu____13404]
                                                   else [] in
                                                 let fail uu____13409 =
                                                   let uu____13410 =
                                                     let uu____13411 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____13412 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____13413 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____13411
                                                       uu____13412
                                                       uu____13413 in
                                                   failwith uu____13410 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____13424) ->
                                                       head_constructor t1
                                                   | uu____13429 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____13431 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____13431
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____13434 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____13451;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____13452;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____13453;_},uu____13454)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____13491 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____13493 =
                                                       let uu____13494 =
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____13494
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____13493]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____13495 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____13503 =
                                                       let uu____13504 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____13504 in
                                                     if uu____13503
                                                     then []
                                                     else
                                                       (let uu____13508 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13508)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____13511 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____13513 =
                                                       let uu____13514 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____13514 in
                                                     if uu____13513
                                                     then []
                                                     else
                                                       (let uu____13518 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13518)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____13544 =
                                                       let uu____13545 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____13545 in
                                                     if uu____13544
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____13552 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____13584
                                                                     ->
                                                                    match uu____13584
                                                                    with
                                                                    | 
                                                                    (ei,uu____13594)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____13600
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____13600
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____13621
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____13635
                                                                    =
                                                                    let uu____13636
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____13637
                                                                    =
                                                                    let uu____13638
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____13638] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____13636
                                                                    uu____13637 in
                                                                    uu____13635
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____13552
                                                            FStar_List.flatten in
                                                        let uu____13647 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____13647
                                                          sub_term_guards)
                                                 | uu____13650 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____13662 =
                                                   let uu____13663 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____13663 in
                                                 if uu____13662
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____13666 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____13666 in
                                                    let uu____13671 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____13671 with
                                                    | (k,uu____13677) ->
                                                        let uu____13678 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____13678
                                                         with
                                                         | (t1,uu____13686,uu____13687)
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
                                          ((let uu____13693 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____13693
                                            then
                                              let uu____13694 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____13694
                                            else ());
                                           (let uu____13696 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____13696, branch_guard, c1,
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
          let uu____13722 = check_let_bound_def true env1 lb in
          (match uu____13722 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____13744 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____13761 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____13761, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____13764 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____13764
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____13768 =
                      let uu____13781 =
                        let uu____13796 =
                          let uu____13805 =
                            let uu____13818 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____13818) in
                          [uu____13805] in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____13796 in
                      FStar_List.hd uu____13781 in
                    match uu____13768 with
                    | (uu____13871,univs1,e11,c11,gvs) ->
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
               (match uu____13744 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____13894 =
                      let uu____13901 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____13901
                      then
                        let uu____13908 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____13908 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____13931 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____13931
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____13932 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____13932, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____13942 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____13942
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm] env1) in
                          let e21 =
                            let uu____13950 =
                              FStar_Syntax_Util.is_pure_comp c in
                            if uu____13950
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
                    (match uu____13894 with
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
                         let uu____13974 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         (uu____13974,
                           (FStar_Syntax_Util.lcomp_of_comp cres),
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____13989 -> failwith "Impossible"
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
            let uu___365_14020 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___365_14020.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___365_14020.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___365_14020.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___365_14020.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___365_14020.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___365_14020.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___365_14020.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___365_14020.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___365_14020.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___365_14020.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___365_14020.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___365_14020.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___365_14020.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___365_14020.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___365_14020.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___365_14020.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___365_14020.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___365_14020.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___365_14020.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___365_14020.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___365_14020.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___365_14020.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___365_14020.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___365_14020.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___365_14020.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___365_14020.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___365_14020.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___365_14020.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___365_14020.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___365_14020.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___365_14020.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___365_14020.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___365_14020.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____14021 =
            let uu____14032 =
              let uu____14033 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____14033 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____14032 lb in
          (match uu____14021 with
           | (e1,uu____14055,c1,g1,annotated) ->
               let x =
                 let uu___366_14060 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___366_14060.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___366_14060.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____14061 =
                 let uu____14066 =
                   let uu____14067 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____14067] in
                 FStar_Syntax_Subst.open_term uu____14066 e2 in
               (match uu____14061 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = FStar_Pervasives_Native.fst xbinder in
                    let uu____14086 =
                      let uu____14093 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____14093 e21 in
                    (match uu____14086 with
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
                           let uu____14112 =
                             let uu____14115 =
                               let uu____14116 =
                                 let uu____14129 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____14129) in
                               FStar_Syntax_Syntax.Tm_let uu____14116 in
                             FStar_Syntax_Syntax.mk uu____14115 in
                           uu____14112 FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____14143 =
                             let uu____14144 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____14145 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____14144
                               c1.FStar_Syntax_Syntax.res_typ uu____14145 e11 in
                           FStar_All.pipe_left
                             (fun _0_42  ->
                                FStar_TypeChecker_Common.NonTrivial _0_42)
                             uu____14143 in
                         let g21 =
                           let uu____14147 =
                             let uu____14148 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____14148 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____14147 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____14150 =
                           let uu____14151 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____14151 in
                         if uu____14150
                         then
                           let tt =
                             let uu____14161 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____14161
                               FStar_Option.get in
                           ((let uu____14167 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____14167
                             then
                               let uu____14168 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____14169 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____14168 uu____14169
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape FStar_Pervasives_Native.None
                                env2 [x1] cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____14174 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____14174
                             then
                               let uu____14175 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____14176 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____14175 uu____14176
                             else ());
                            (e4,
                              ((let uu___367_14179 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___367_14179.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___367_14179.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___367_14179.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____14180 -> failwith "Impossible"
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
          let uu____14212 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____14212 with
           | (lbs1,e21) ->
               let uu____14231 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____14231 with
                | (env0,topt) ->
                    let uu____14250 = build_let_rec_env true env0 lbs1 in
                    (match uu____14250 with
                     | (lbs2,rec_env) ->
                         let uu____14269 = check_let_recs rec_env lbs2 in
                         (match uu____14269 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____14289 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____14289
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____14295 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____14295
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
                                     let uu____14344 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____14384 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____14384))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____14344 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____14433  ->
                                           match uu____14433 with
                                           | (x,uvs,e,c,gvs) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____14480 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____14480 in
                              let uu____14485 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                              (match uu____14485 with
                               | (lbs5,e22) ->
                                   ((let uu____14505 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1 in
                                     FStar_All.pipe_right uu____14505
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____14506 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     (uu____14506, cres,
                                       FStar_TypeChecker_Rel.trivial_guard))))))))
      | uu____14519 -> failwith "Impossible"
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
          let uu____14551 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____14551 with
           | (lbs1,e21) ->
               let uu____14570 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____14570 with
                | (env0,topt) ->
                    let uu____14589 = build_let_rec_env false env0 lbs1 in
                    (match uu____14589 with
                     | (lbs2,rec_env) ->
                         let uu____14608 = check_let_recs rec_env lbs2 in
                         (match uu____14608 with
                          | (lbs3,g_lbs) ->
                              let uu____14627 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___368_14650 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___368_14650.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___368_14650.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___369_14652 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___369_14652.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___369_14652.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___369_14652.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___369_14652.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____14627 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____14679 = tc_term env2 e21 in
                                   (match uu____14679 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____14696 =
                                            let uu____14697 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____14697 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____14696 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___370_14701 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___370_14701.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___370_14701.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___370_14701.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____14702 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____14702 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____14738 ->
                                                  (e, cres2, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  let cres3 =
                                                    let uu___371_14743 =
                                                      cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___371_14743.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___371_14743.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___371_14743.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____14746 -> failwith "Impossible"
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
          let uu____14775 = FStar_Options.ml_ish () in
          if uu____14775
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp in
             let uu____14778 =
               let uu____14783 =
                 let uu____14784 = FStar_Syntax_Subst.compress t in
                 uu____14784.FStar_Syntax_Syntax.n in
               let uu____14787 =
                 let uu____14788 = FStar_Syntax_Subst.compress lbdef in
                 uu____14788.FStar_Syntax_Syntax.n in
               (uu____14783, uu____14787) in
             match uu____14778 with
             | (FStar_Syntax_Syntax.Tm_arrow
                (formals,c),FStar_Syntax_Syntax.Tm_abs
                (actuals,uu____14794,uu____14795)) ->
                 let actuals1 =
                   let uu____14833 =
                     FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                   FStar_TypeChecker_Util.maybe_add_implicit_binders
                     uu____14833 actuals in
                 (if
                    (FStar_List.length formals) <>
                      (FStar_List.length actuals1)
                  then
                    (let actuals_msg =
                       let n1 = FStar_List.length actuals1 in
                       if n1 = (Prims.parse_int "1")
                       then "1 argument was found"
                       else
                         (let uu____14854 = FStar_Util.string_of_int n1 in
                          FStar_Util.format1 "%s arguments were found"
                            uu____14854) in
                     let formals_msg =
                       let n1 = FStar_List.length formals in
                       if n1 = (Prims.parse_int "1")
                       then "1 argument"
                       else
                         (let uu____14872 = FStar_Util.string_of_int n1 in
                          FStar_Util.format1 "%s arguments" uu____14872) in
                     let msg =
                       let uu____14880 =
                         FStar_Syntax_Print.term_to_string lbtyp in
                       let uu____14881 =
                         FStar_Syntax_Print.lbname_to_string lbname in
                       FStar_Util.format4
                         "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                         uu____14880 uu____14881 formals_msg actuals_msg in
                     FStar_Exn.raise
                       (FStar_Errors.Error
                          (msg, (lbdef.FStar_Syntax_Syntax.pos))))
                  else ();
                  (let quals =
                     FStar_TypeChecker_Env.lookup_effect_quals env
                       (FStar_Syntax_Util.comp_effect_name c) in
                   FStar_All.pipe_right quals
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
             | uu____14888 ->
                 let uu____14893 =
                   let uu____14894 =
                     let uu____14899 =
                       let uu____14900 =
                         FStar_Syntax_Print.term_to_string lbdef in
                       let uu____14901 =
                         FStar_Syntax_Print.term_to_string lbtyp in
                       FStar_Util.format2
                         "Only function literals with arrow types can be defined recursively; got %s : %s"
                         uu____14900 uu____14901 in
                     (uu____14899, (lbtyp.FStar_Syntax_Syntax.pos)) in
                   FStar_Errors.Error uu____14894 in
                 FStar_Exn.raise uu____14893) in
        let uu____14902 =
          FStar_List.fold_left
            (fun uu____14928  ->
               fun lb  ->
                 match uu____14928 with
                 | (lbs1,env1) ->
                     let uu____14948 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____14948 with
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
                              (let uu____14968 =
                                 let uu____14975 =
                                   let uu____14976 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____14976 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___372_14987 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___372_14987.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___372_14987.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___372_14987.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___372_14987.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___372_14987.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___372_14987.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___372_14987.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___372_14987.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___372_14987.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___372_14987.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___372_14987.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___372_14987.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___372_14987.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___372_14987.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___372_14987.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___372_14987.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___372_14987.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___372_14987.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___372_14987.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___372_14987.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___372_14987.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___372_14987.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___372_14987.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___372_14987.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___372_14987.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___372_14987.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___372_14987.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___372_14987.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___372_14987.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___372_14987.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___372_14987.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___372_14987.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___372_14987.FStar_TypeChecker_Env.dep_graph)
                                    }) t uu____14975 in
                               match uu____14968 with
                               | (t1,uu____14989,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____14993 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____14993);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____14995 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____14995
                            then
                              let uu___373_14996 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___373_14996.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___373_14996.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___373_14996.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___373_14996.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___373_14996.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___373_14996.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___373_14996.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___373_14996.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___373_14996.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___373_14996.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___373_14996.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___373_14996.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1,
                                     univ_vars1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___373_14996.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___373_14996.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___373_14996.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___373_14996.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___373_14996.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___373_14996.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___373_14996.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___373_14996.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___373_14996.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___373_14996.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___373_14996.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___373_14996.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___373_14996.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___373_14996.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___373_14996.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___373_14996.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___373_14996.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___373_14996.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___373_14996.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___373_14996.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___373_14996.FStar_TypeChecker_Env.dep_graph)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname
                                (univ_vars1, t1) in
                          let lb1 =
                            let uu___374_15013 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___374_15013.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___374_15013.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____14902 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lbs  ->
      let uu____15036 =
        let uu____15045 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____15074 =
                     let uu____15075 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____15075.FStar_Syntax_Syntax.n in
                   match uu____15074 with
                   | FStar_Syntax_Syntax.Tm_abs uu____15078 -> ()
                   | uu____15095 ->
                       let uu____15096 =
                         let uu____15097 =
                           let uu____15102 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____15102) in
                         FStar_Errors.Error uu____15097 in
                       FStar_Exn.raise uu____15096);
                  (let uu____15103 =
                     let uu____15110 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____15110
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____15103 with
                   | (e,c,g) ->
                       ((let uu____15119 =
                           let uu____15120 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____15120 in
                         if uu____15119
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
        FStar_All.pipe_right uu____15045 FStar_List.unzip in
      match uu____15036 with
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
        let uu____15169 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____15169 with
        | (env1,uu____15187) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____15195 = check_lbtyp top_level env lb in
            (match uu____15195 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Exn.raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____15239 =
                     tc_maybe_toplevel_term
                       (let uu___375_15248 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___375_15248.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___375_15248.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___375_15248.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___375_15248.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___375_15248.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___375_15248.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___375_15248.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___375_15248.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___375_15248.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___375_15248.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___375_15248.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___375_15248.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___375_15248.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___375_15248.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___375_15248.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___375_15248.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___375_15248.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___375_15248.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___375_15248.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.failhard =
                            (uu___375_15248.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___375_15248.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___375_15248.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___375_15248.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___375_15248.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___375_15248.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___375_15248.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___375_15248.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___375_15248.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___375_15248.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___375_15248.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___375_15248.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___375_15248.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___375_15248.FStar_TypeChecker_Env.dep_graph)
                        }) e11 in
                   match uu____15239 with
                   | (e12,c1,g1) ->
                       let uu____15262 =
                         let uu____15267 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____15271  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____15267 e12 c1 wf_annot in
                       (match uu____15262 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____15286 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____15286
                              then
                                let uu____15287 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____15288 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____15289 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____15287 uu____15288 uu____15289
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
        | uu____15333 ->
            let uu____15334 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____15334 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____15383 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____15383)
                 else
                   (let uu____15391 = FStar_Syntax_Util.type_u () in
                    match uu____15391 with
                    | (k,uu____15411) ->
                        let uu____15412 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____15412 with
                         | (t2,uu____15434,g) ->
                             ((let uu____15437 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____15437
                               then
                                 let uu____15438 =
                                   let uu____15439 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____15439 in
                                 let uu____15440 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____15438 uu____15440
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____15443 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____15443))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun uu____15451  ->
      match uu____15451 with
      | (x,imp) ->
          let uu____15470 = FStar_Syntax_Util.type_u () in
          (match uu____15470 with
           | (tu,u) ->
               ((let uu____15490 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____15490
                 then
                   let uu____15491 = FStar_Syntax_Print.bv_to_string x in
                   let uu____15492 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____15493 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____15491 uu____15492 uu____15493
                 else ());
                (let uu____15495 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____15495 with
                 | (t,uu____15515,g) ->
                     let x1 =
                       ((let uu___376_15523 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___376_15523.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___376_15523.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____15525 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____15525
                       then
                         let uu____15526 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1) in
                         let uu____15527 =
                           FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____15526 uu____15527
                       else ());
                      (let uu____15529 = push_binding env x1 in
                       (x1, uu____15529, g, u))))))
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
            let uu____15619 = tc_binder env1 b in
            (match uu____15619 with
             | (b1,env',g,u) ->
                 let uu____15660 = aux env' bs2 in
                 (match uu____15660 with
                  | (bs3,env'1,g',us) ->
                      let uu____15713 =
                        let uu____15714 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____15714 in
                      ((b1 :: bs3), env'1, uu____15713, (u :: us)))) in
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
          (fun uu____15799  ->
             fun uu____15800  ->
               match (uu____15799, uu____15800) with
               | ((t,imp),(args1,g)) ->
                   let uu____15869 = tc_term env1 t in
                   (match uu____15869 with
                    | (t1,uu____15887,g') ->
                        let uu____15889 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____15889))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____15931  ->
             match uu____15931 with
             | (pats1,g) ->
                 let uu____15956 = tc_args env p in
                 (match uu____15956 with
                  | (args,g') ->
                      let uu____15969 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____15969))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let uu____15982 = tc_maybe_toplevel_term env e in
      match uu____15982 with
      | (e1,c,g) ->
          let uu____15998 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____15998
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____16011 =
               let uu____16016 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____16016
               then
                 let uu____16021 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____16021, false)
               else
                 (let uu____16023 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____16023, true)) in
             match uu____16011 with
             | (target_comp,allow_ghost) ->
                 let uu____16032 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____16032 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____16042 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____16042)
                  | uu____16043 ->
                      if allow_ghost
                      then
                        let uu____16052 =
                          let uu____16053 =
                            let uu____16058 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____16058, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____16053 in
                        FStar_Exn.raise uu____16052
                      else
                        (let uu____16066 =
                           let uu____16067 =
                             let uu____16072 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____16072, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____16067 in
                         FStar_Exn.raise uu____16066)))
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
      let uu____16091 = tc_tot_or_gtot_term env t in
      match uu____16091 with
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
      (let uu____16119 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____16119
       then
         let uu____16120 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____16120
       else ());
      (let env1 =
         let uu___377_16123 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___377_16123.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___377_16123.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___377_16123.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___377_16123.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___377_16123.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___377_16123.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___377_16123.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___377_16123.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___377_16123.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___377_16123.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___377_16123.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___377_16123.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___377_16123.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___377_16123.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___377_16123.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___377_16123.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___377_16123.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___377_16123.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___377_16123.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___377_16123.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___377_16123.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___377_16123.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___377_16123.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___377_16123.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___377_16123.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___377_16123.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___377_16123.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___377_16123.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___377_16123.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___377_16123.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___377_16123.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___377_16123.FStar_TypeChecker_Env.dep_graph)
         } in
       let uu____16130 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____16163) ->
             let uu____16164 =
               let uu____16165 =
                 let uu____16170 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____16170) in
               FStar_Errors.Error uu____16165 in
             FStar_Exn.raise uu____16164 in
       match uu____16130 with
       | (t,c,g) ->
           let uu____16186 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____16186
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____16196 =
                let uu____16197 =
                  let uu____16202 =
                    let uu____16203 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____16203 in
                  let uu____16204 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____16202, uu____16204) in
                FStar_Errors.Error uu____16197 in
              FStar_Exn.raise uu____16196))
let level_of_type_fail:
  'Auu____16215 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____16215
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____16228 =
          let uu____16229 =
            let uu____16234 =
              let uu____16235 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format2
                "Expected a term of type 'Type'; got %s : %s" uu____16235 t in
            let uu____16236 = FStar_TypeChecker_Env.get_range env in
            (uu____16234, uu____16236) in
          FStar_Errors.Error uu____16229 in
        FStar_Exn.raise uu____16228
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____16253 =
            let uu____16254 = FStar_Syntax_Util.unrefine t1 in
            uu____16254.FStar_Syntax_Syntax.n in
          match uu____16253 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____16258 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____16261 = FStar_Syntax_Util.type_u () in
                 match uu____16261 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___380_16269 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___380_16269.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___380_16269.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___380_16269.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___380_16269.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___380_16269.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___380_16269.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___380_16269.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___380_16269.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___380_16269.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___380_16269.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___380_16269.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___380_16269.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___380_16269.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___380_16269.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___380_16269.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___380_16269.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___380_16269.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___380_16269.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___380_16269.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___380_16269.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___380_16269.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___380_16269.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___380_16269.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___380_16269.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___380_16269.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___380_16269.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___380_16269.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___380_16269.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___380_16269.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___380_16269.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___380_16269.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___380_16269.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___380_16269.FStar_TypeChecker_Env.dep_graph)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____16273 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____16273
                       | uu____16274 ->
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
      let uu____16283 =
        let uu____16284 = FStar_Syntax_Subst.compress e in
        uu____16284.FStar_Syntax_Syntax.n in
      match uu____16283 with
      | FStar_Syntax_Syntax.Tm_bvar uu____16289 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____16294 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____16321 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____16337) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____16360,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____16387) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____16394 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____16394 with | ((uu____16405,t),uu____16407) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16412,(FStar_Util.Inl t,uu____16414),uu____16415) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16462,(FStar_Util.Inr c,uu____16464),uu____16465) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____16515;
             FStar_Syntax_Syntax.vars = uu____16516;_},us)
          ->
          let uu____16522 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____16522 with
           | ((us',t),uu____16535) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____16541 =
                     let uu____16542 =
                       let uu____16547 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____16547) in
                     FStar_Errors.Error uu____16542 in
                   FStar_Exn.raise uu____16541)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____16563 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____16564 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____16574) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____16597 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____16597 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____16617  ->
                      match uu____16617 with
                      | (b,uu____16623) ->
                          let uu____16624 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____16624) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____16629 = universe_of_aux env res in
                 level_of_type env res uu____16629 in
               let u_c =
                 let uu____16631 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____16631 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____16635 = universe_of_aux env trepr in
                     level_of_type env trepr uu____16635 in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____16728 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____16743 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____16782 ->
                let uu____16783 = universe_of_aux env hd3 in
                (uu____16783, args1)
            | FStar_Syntax_Syntax.Tm_name uu____16796 ->
                let uu____16797 = universe_of_aux env hd3 in
                (uu____16797, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____16810 ->
                let uu____16827 = universe_of_aux env hd3 in
                (uu____16827, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____16840 ->
                let uu____16847 = universe_of_aux env hd3 in
                (uu____16847, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____16860 ->
                let uu____16887 = universe_of_aux env hd3 in
                (uu____16887, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____16900 ->
                let uu____16907 = universe_of_aux env hd3 in
                (uu____16907, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____16920 ->
                let uu____16921 = universe_of_aux env hd3 in
                (uu____16921, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____16934 ->
                let uu____16947 = universe_of_aux env hd3 in
                (uu____16947, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____16960 ->
                let uu____16967 = universe_of_aux env hd3 in
                (uu____16967, args1)
            | FStar_Syntax_Syntax.Tm_type uu____16980 ->
                let uu____16981 = universe_of_aux env hd3 in
                (uu____16981, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____16994,hd4::uu____16996) ->
                let uu____17061 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____17061 with
                 | (uu____17076,uu____17077,hd5) ->
                     let uu____17095 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____17095 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____17146 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____17148 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____17148 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____17199 ->
                let uu____17200 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____17200 with
                 | (env1,uu____17222) ->
                     let env2 =
                       let uu___381_17228 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___381_17228.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___381_17228.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___381_17228.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___381_17228.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___381_17228.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___381_17228.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___381_17228.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___381_17228.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___381_17228.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___381_17228.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___381_17228.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___381_17228.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___381_17228.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___381_17228.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___381_17228.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___381_17228.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___381_17228.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___381_17228.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___381_17228.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___381_17228.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___381_17228.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___381_17228.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___381_17228.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___381_17228.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___381_17228.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___381_17228.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___381_17228.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___381_17228.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___381_17228.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___381_17228.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___381_17228.FStar_TypeChecker_Env.dep_graph)
                       } in
                     ((let uu____17230 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____17230
                       then
                         let uu____17231 =
                           let uu____17232 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____17232 in
                         let uu____17233 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____17231 uu____17233
                       else ());
                      (let uu____17235 = tc_term env2 hd3 in
                       match uu____17235 with
                       | (uu____17256,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____17257;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____17259;
                                        FStar_Syntax_Syntax.comp =
                                          uu____17260;_},g)
                           ->
                           ((let uu____17271 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____17271
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____17282 = type_of_head true hd1 args in
          (match uu____17282 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____17322 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____17322 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____17366 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____17366)))
      | FStar_Syntax_Syntax.Tm_match (uu____17369,hd1::uu____17371) ->
          let uu____17436 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____17436 with
           | (uu____17439,uu____17440,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____17458,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____17501 = universe_of_aux env e in
      level_of_type env e uu____17501
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tps  ->
      let uu____17520 = tc_binders env tps in
      match uu____17520 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))