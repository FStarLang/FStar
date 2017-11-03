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
                                   (fun _0_39  ->
                                      FStar_Pervasives_Native.Some _0_39)
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
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        let uu____953 =
          let uu____954 = FStar_TypeChecker_Env.should_verify env in
          Prims.op_Negation uu____954 in
        if uu____953
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env in
               let env1 =
                 let uu___339_985 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___339_985.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___339_985.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___339_985.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___339_985.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___339_985.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___339_985.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___339_985.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___339_985.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___339_985.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___339_985.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___339_985.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___339_985.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___339_985.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___339_985.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___339_985.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___339_985.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___339_985.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___339_985.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___339_985.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___339_985.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___339_985.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___339_985.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___339_985.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___339_985.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___339_985.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___339_985.FStar_TypeChecker_Env.qname_and_index);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___339_985.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth =
                     (uu___339_985.FStar_TypeChecker_Env.synth);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___339_985.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___339_985.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___339_985.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___339_985.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___339_985.FStar_TypeChecker_Env.dep_graph)
                 } in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Parser_Const.precedes_lid in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____1019  ->
                           match uu____1019 with
                           | (b,uu____1027) ->
                               let t =
                                 let uu____1029 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort in
                                 FStar_TypeChecker_Normalize.unfold_whnf env1
                                   uu____1029 in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type uu____1032 ->
                                    []
                                | FStar_Syntax_Syntax.Tm_arrow uu____1033 ->
                                    []
                                | uu____1046 ->
                                    let uu____1047 =
                                      FStar_Syntax_Syntax.bv_to_name b in
                                    [uu____1047]))) in
                 let as_lex_list dec =
                   let uu____1052 = FStar_Syntax_Util.head_and_args dec in
                   match uu____1052 with
                   | (head1,uu____1068) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.lexcons_lid
                            -> dec
                        | uu____1090 -> mk_lex_list [dec]) in
                 let cflags = FStar_Syntax_Util.comp_flags c in
                 let uu____1094 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___332_1103  ->
                           match uu___332_1103 with
                           | FStar_Syntax_Syntax.DECREASES uu____1104 -> true
                           | uu____1107 -> false)) in
                 match uu____1094 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.DECREASES dec) -> as_lex_list dec
                 | uu____1111 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions in
                     (match xs with
                      | x::[] -> x
                      | uu____1120 -> mk_lex_list xs) in
               let previous_dec = decreases_clause actuals expected_c in
               let guard_one_letrec uu____1137 =
                 match uu____1137 with
                 | (l,t) ->
                     let uu____1150 =
                       let uu____1151 = FStar_Syntax_Subst.compress t in
                       uu____1151.FStar_Syntax_Syntax.n in
                     (match uu____1150 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____1210  ->
                                    match uu____1210 with
                                    | (x,imp) ->
                                        let uu____1221 =
                                          FStar_Syntax_Syntax.is_null_bv x in
                                        if uu____1221
                                        then
                                          let uu____1226 =
                                            let uu____1227 =
                                              let uu____1230 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x in
                                              FStar_Pervasives_Native.Some
                                                uu____1230 in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____1227
                                              x.FStar_Syntax_Syntax.sort in
                                          (uu____1226, imp)
                                        else (x, imp))) in
                          let uu____1232 =
                            FStar_Syntax_Subst.open_comp formals1 c in
                          (match uu____1232 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1 in
                               let precedes1 =
                                 let uu____1249 =
                                   let uu____1250 =
                                     let uu____1251 =
                                       FStar_Syntax_Syntax.as_arg dec in
                                     let uu____1252 =
                                       let uu____1255 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec in
                                       [uu____1255] in
                                     uu____1251 :: uu____1252 in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____1250 in
                                 uu____1249 FStar_Pervasives_Native.None r in
                               let uu____1258 = FStar_Util.prefix formals2 in
                               (match uu____1258 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___340_1303 = last1 in
                                      let uu____1304 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1 in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___340_1303.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___340_1303.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____1304
                                      } in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)] in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1 in
                                    ((let uu____1330 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low in
                                      if uu____1330
                                      then
                                        let uu____1331 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l in
                                        let uu____1332 =
                                          FStar_Syntax_Print.term_to_string t in
                                        let uu____1333 =
                                          FStar_Syntax_Print.term_to_string
                                            t' in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____1331 uu____1332 uu____1333
                                      else ());
                                     (l, t'))))
                      | uu____1337 ->
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
        (let uu___341_1768 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___341_1768.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___341_1768.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___341_1768.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___341_1768.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___341_1768.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___341_1768.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___341_1768.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___341_1768.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___341_1768.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___341_1768.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___341_1768.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___341_1768.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___341_1768.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___341_1768.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___341_1768.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___341_1768.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___341_1768.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___341_1768.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___341_1768.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___341_1768.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___341_1768.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___341_1768.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___341_1768.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___341_1768.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___341_1768.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___341_1768.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___341_1768.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___341_1768.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___341_1768.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___341_1768.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___341_1768.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___341_1768.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___341_1768.FStar_TypeChecker_Env.dep_graph)
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
      (let uu____1780 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1780
       then
         let uu____1781 =
           let uu____1782 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1782 in
         let uu____1783 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1781 uu____1783
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1792 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1823 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1830 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1847 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1848 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1849 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1850 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1851 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1868 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1881 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1888 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____1889;
              FStar_Syntax_Syntax.vars = uu____1890;_},FStar_Syntax_Syntax.Meta_alien
            (uu____1891,uu____1892,ty))
           ->
           let uu____1902 =
             let uu____1903 = FStar_Syntax_Syntax.mk_Total ty in
             FStar_All.pipe_right uu____1903 FStar_Syntax_Util.lcomp_of_comp in
           (top, uu____1902, FStar_TypeChecker_Rel.trivial_guard)
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1909 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1909 with
            | (e2,c,g) ->
                let g1 =
                  let uu___342_1926 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___342_1926.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___342_1926.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___342_1926.FStar_TypeChecker_Env.implicits)
                  } in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1943 = FStar_Syntax_Util.type_u () in
           (match uu____1943 with
            | (t,u) ->
                let uu____1956 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1956 with
                 | (e2,c,g) ->
                     let uu____1972 =
                       let uu____1987 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____1987 with
                       | (env2,uu____2009) -> tc_pats env2 pats in
                     (match uu____1972 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___343_2043 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___343_2043.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___343_2043.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___343_2043.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____2044 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____2047 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____2044, c, uu____2047))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____2055 =
             let uu____2056 = FStar_Syntax_Subst.compress e1 in
             uu____2056.FStar_Syntax_Syntax.n in
           (match uu____2055 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____2065,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____2067;
                               FStar_Syntax_Syntax.lbtyp = uu____2068;
                               FStar_Syntax_Syntax.lbeff = uu____2069;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____2094 =
                  let uu____2101 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit in
                  tc_term uu____2101 e11 in
                (match uu____2094 with
                 | (e12,c1,g1) ->
                     let uu____2111 = tc_term env1 e2 in
                     (match uu____2111 with
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
                            let uu____2135 =
                              let uu____2138 =
                                let uu____2139 =
                                  let uu____2152 =
                                    let uu____2159 =
                                      let uu____2162 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13) in
                                      [uu____2162] in
                                    (false, uu____2159) in
                                  (uu____2152, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____2139 in
                              FStar_Syntax_Syntax.mk uu____2138 in
                            uu____2135 FStar_Pervasives_Native.None
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
                          let uu____2184 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____2184)))
            | uu____2187 ->
                let uu____2188 = tc_term env1 e1 in
                (match uu____2188 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2210) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____2227 = tc_term env1 e1 in
           (match uu____2227 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____2251) ->
           let uu____2298 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2298 with
            | (env0,uu____2312) ->
                let uu____2317 = tc_comp env0 expected_c in
                (match uu____2317 with
                 | (expected_c1,uu____2331,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____2336 =
                       let uu____2343 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____2343 e1 in
                     (match uu____2336 with
                      | (e2,c',g') ->
                          let uu____2353 =
                            let uu____2360 =
                              let uu____2365 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____2365) in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____2360 in
                          (match uu____2353 with
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
                                 let uu____2420 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____2420 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____2429 =
                                            FStar_Syntax_Util.mk_squash f1 in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____2429) in
                               let uu____2430 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____2430 with
                                | (e5,c,f2) ->
                                    let final_guard =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, final_guard))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____2450) ->
           let uu____2497 = FStar_Syntax_Util.type_u () in
           (match uu____2497 with
            | (k,u) ->
                let uu____2510 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____2510 with
                 | (t1,uu____2524,f) ->
                     let uu____2526 =
                       let uu____2533 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____2533 e1 in
                     (match uu____2526 with
                      | (e2,c,g) ->
                          let uu____2543 =
                            let uu____2548 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____2552  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____2548 e2 c f in
                          (match uu____2543 with
                           | (c1,f1) ->
                               let uu____2561 =
                                 let uu____2568 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2,
                                          ((FStar_Util.Inl t1),
                                            FStar_Pervasives_Native.None),
                                          (FStar_Pervasives_Native.Some
                                             (c1.FStar_Syntax_Syntax.eff_name))))
                                     FStar_Pervasives_Native.None
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____2568 c1 in
                               (match uu____2561 with
                                | (e3,c2,f2) ->
                                    let uu____2608 =
                                      let uu____2609 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____2609 in
                                    (e3, c2, uu____2608))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____2610;
              FStar_Syntax_Syntax.vars = uu____2611;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2674 = FStar_Syntax_Util.head_and_args top in
           (match uu____2674 with
            | (unary_op,uu____2696) ->
                let head1 =
                  let uu____2720 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2720 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____2758;
              FStar_Syntax_Syntax.vars = uu____2759;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2822 = FStar_Syntax_Util.head_and_args top in
           (match uu____2822 with
            | (unary_op,uu____2844) ->
                let head1 =
                  let uu____2868 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2868 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____2906);
              FStar_Syntax_Syntax.pos = uu____2907;
              FStar_Syntax_Syntax.vars = uu____2908;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2971 = FStar_Syntax_Util.head_and_args top in
           (match uu____2971 with
            | (unary_op,uu____2993) ->
                let head1 =
                  let uu____3017 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3017 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3055;
              FStar_Syntax_Syntax.vars = uu____3056;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____3132 = FStar_Syntax_Util.head_and_args top in
           (match uu____3132 with
            | (unary_op,uu____3154) ->
                let head1 =
                  let uu____3178 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____3178 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3222;
              FStar_Syntax_Syntax.vars = uu____3223;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____3261 =
             let uu____3268 =
               let uu____3269 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3269 in
             tc_term uu____3268 e1 in
           (match uu____3261 with
            | (e2,c,g) ->
                let uu____3293 = FStar_Syntax_Util.head_and_args top in
                (match uu____3293 with
                 | (head1,uu____3315) ->
                     let uu____3336 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos in
                     let uu____3363 =
                       let uu____3364 =
                         let uu____3367 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid in
                         FStar_Syntax_Syntax.mk_Total uu____3367 in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____3364 in
                     (uu____3336, uu____3363, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3372;
              FStar_Syntax_Syntax.vars = uu____3373;_},(a1,FStar_Pervasives_Native.None
                                                        )::(a2,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____3426 = FStar_Syntax_Util.head_and_args top in
           (match uu____3426 with
            | (head1,uu____3448) ->
                let env' =
                  let uu____3470 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____3470 in
                let uu____3471 = tc_term env' a1 in
                (match uu____3471 with
                 | (e1,uu____3485,g1) ->
                     let uu____3487 = tc_term env1 a2 in
                     (match uu____3487 with
                      | (e2,t2,g2) ->
                          let g = FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          let uu____3504 =
                            let uu____3507 =
                              let uu____3508 =
                                let uu____3509 =
                                  FStar_Syntax_Syntax.as_arg a1 in
                                let uu____3510 =
                                  let uu____3513 =
                                    FStar_Syntax_Syntax.as_arg a2 in
                                  [uu____3513] in
                                uu____3509 :: uu____3510 in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____3508 in
                            uu____3507 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          (uu____3504, t2, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3518;
              FStar_Syntax_Syntax.vars = uu____3519;_},uu____3520)
           ->
           let uu____3541 =
             let uu____3542 =
               let uu____3547 =
                 let uu____3548 = FStar_Syntax_Print.term_to_string top in
                 FStar_Util.format1 "Ill-applied constant %s" uu____3548 in
               (uu____3547, (e.FStar_Syntax_Syntax.pos)) in
             FStar_Errors.Error uu____3542 in
           FStar_Exn.raise uu____3541
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3555;
              FStar_Syntax_Syntax.vars = uu____3556;_},uu____3557)
           ->
           let uu____3578 =
             let uu____3579 =
               let uu____3584 =
                 let uu____3585 = FStar_Syntax_Print.term_to_string top in
                 FStar_Util.format1 "Ill-applied constant %s" uu____3585 in
               (uu____3584, (e.FStar_Syntax_Syntax.pos)) in
             FStar_Errors.Error uu____3579 in
           FStar_Exn.raise uu____3578
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____3592;
              FStar_Syntax_Syntax.vars = uu____3593;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____3626 =
               let uu____3633 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____3633 with | (env0,uu____3647) -> tc_term env0 e1 in
             match uu____3626 with
             | (e2,c,g) ->
                 let uu____3661 = FStar_Syntax_Util.head_and_args top in
                 (match uu____3661 with
                  | (reify_op,uu____3683) ->
                      let u_c =
                        let uu____3705 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____3705 with
                        | (uu____3712,c',uu____3714) ->
                            let uu____3715 =
                              let uu____3716 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____3716.FStar_Syntax_Syntax.n in
                            (match uu____3715 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____3720 ->
                                 let uu____3721 = FStar_Syntax_Util.type_u () in
                                 (match uu____3721 with
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
                                            let uu____3733 =
                                              let uu____3734 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____3735 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____3736 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____3734 uu____3735
                                                uu____3736 in
                                            failwith uu____3733);
                                       u))) in
                      let repr =
                        let uu____3738 = c.FStar_Syntax_Syntax.comp () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____3738 u_c in
                      let e3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (reify_op, [(e2, aqual)]))
                          FStar_Pervasives_Native.None
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____3759 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____3759
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____3760 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____3760 with
                       | (e4,c2,g') ->
                           let uu____3776 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____3776)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____3778;
              FStar_Syntax_Syntax.vars = uu____3779;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____3821 =
               let uu____3822 =
                 let uu____3823 =
                   let uu____3828 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____3828, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____3823 in
               FStar_Exn.raise uu____3822 in
             let uu____3835 = FStar_Syntax_Util.head_and_args top in
             match uu____3835 with
             | (reflect_op,uu____3857) ->
                 let uu____3878 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____3878 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____3911 =
                        let uu____3912 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____3912 in
                      if uu____3911
                      then no_reflect ()
                      else
                        (let uu____3922 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____3922 with
                         | (env_no_ex,topt) ->
                             let uu____3941 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____3961 =
                                   let uu____3964 =
                                     let uu____3965 =
                                       let uu____3980 =
                                         let uu____3983 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____3984 =
                                           let uu____3987 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____3987] in
                                         uu____3983 :: uu____3984 in
                                       (repr, uu____3980) in
                                     FStar_Syntax_Syntax.Tm_app uu____3965 in
                                   FStar_Syntax_Syntax.mk uu____3964 in
                                 uu____3961 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos in
                               let uu____3993 =
                                 let uu____4000 =
                                   let uu____4001 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____4001
                                     FStar_Pervasives_Native.fst in
                                 tc_tot_or_gtot_term uu____4000 t in
                               match uu____3993 with
                               | (t1,uu____4029,g) ->
                                   let uu____4031 =
                                     let uu____4032 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____4032.FStar_Syntax_Syntax.n in
                                   (match uu____4031 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____4047,(res,uu____4049)::
                                         (wp,uu____4051)::[])
                                        -> (t1, res, wp, g)
                                    | uu____4094 -> failwith "Impossible") in
                             (match uu____3941 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____4125 =
                                    let uu____4130 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____4130 with
                                    | (e2,c,g) ->
                                        ((let uu____4145 =
                                            let uu____4146 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____4146 in
                                          if uu____4145
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____4156 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____4156 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____4164 =
                                                  let uu____4171 =
                                                    let uu____4176 =
                                                      let uu____4177 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____4178 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____4177 uu____4178 in
                                                    (uu____4176,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____4171] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____4164);
                                               (let uu____4187 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____4187)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____4189 =
                                                let uu____4190 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____4190 in
                                              (e2, uu____4189))) in
                                  (match uu____4125 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____4200 =
                                           let uu____4201 =
                                             let uu____4202 =
                                               let uu____4203 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____4203] in
                                             let uu____4204 =
                                               let uu____4213 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____4213] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____4202;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____4204;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____4201 in
                                         FStar_All.pipe_right uu____4200
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____4233 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____4233 with
                                        | (e4,c1,g') ->
                                            let uu____4249 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____4249))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____4296 =
               let uu____4297 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____4297 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____4296 instantiate_both in
           ((let uu____4313 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____4313
             then
               let uu____4314 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____4315 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____4314
                 uu____4315
             else ());
            (let isquote =
               let uu____4318 = FStar_Syntax_Util.head_and_args head1 in
               match uu____4318 with
               | (head2,uu____4334) ->
                   let uu____4355 =
                     let uu____4356 = FStar_Syntax_Util.un_uinst head2 in
                     uu____4356.FStar_Syntax_Syntax.n in
                   (match uu____4355 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.quote_lid
                        -> true
                    | uu____4360 -> false) in
             let uu____4361 = tc_term (no_inst env2) head1 in
             match uu____4361 with
             | (head2,chead,g_head) ->
                 let uu____4377 =
                   let uu____4384 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____4384
                   then
                     let uu____4391 =
                       let uu____4398 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____4398 in
                     match uu____4391 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____4411 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____4413 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c in
                                 Prims.op_Negation uu____4413))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                           if uu____4411
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c in
                         (e1, c1, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2 in
                      let uu____4418 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env3 head2 chead g_head args
                        uu____4418) in
                 (match uu____4377 with
                  | (e1,c,g) ->
                      ((let uu____4431 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____4431
                        then
                          let uu____4432 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____4432
                        else ());
                       (let uu____4434 = comp_check_expected_typ env0 e1 c in
                        match uu____4434 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____4451 =
                                let uu____4452 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____4452.FStar_Syntax_Syntax.n in
                              match uu____4451 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____4456) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___344_4518 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___344_4518.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___344_4518.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___344_4518.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____4567 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____4569 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____4569 in
                            ((let uu____4571 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____4571
                              then
                                let uu____4572 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____4573 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____4572 uu____4573
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____4613 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____4613 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____4633 = tc_term env12 e1 in
                (match uu____4633 with
                 | (e11,c1,g1) ->
                     let uu____4649 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____4659 = FStar_Syntax_Util.type_u () in
                           (match uu____4659 with
                            | (k,uu____4669) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____4671 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____4671, res_t)) in
                     (match uu____4649 with
                      | (env_branches,res_t) ->
                          ((let uu____4681 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____4681
                            then
                              let uu____4682 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____4682
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____4768 =
                              let uu____4773 =
                                FStar_List.fold_right
                                  (fun uu____4819  ->
                                     fun uu____4820  ->
                                       match (uu____4819, uu____4820) with
                                       | ((uu____4883,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____4943 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____4943))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____4773 with
                              | (cases,g) ->
                                  let uu____4982 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____4982, g) in
                            match uu____4768 with
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
                                           (fun uu____5078  ->
                                              match uu____5078 with
                                              | ((pat,wopt,br),uu____5106,lc,uu____5108)
                                                  ->
                                                  let uu____5121 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____5121))) in
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
                                  let uu____5176 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____5176
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____5183 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____5183 in
                                     let lb =
                                       let uu____5187 =
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
                                           uu____5187;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____5191 =
                                         let uu____5194 =
                                           let uu____5195 =
                                             let uu____5208 =
                                               let uu____5209 =
                                                 let uu____5210 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____5210] in
                                               FStar_Syntax_Subst.close
                                                 uu____5209 e_match in
                                             ((false, [lb]), uu____5208) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____5195 in
                                         FStar_Syntax_Syntax.mk uu____5194 in
                                       uu____5191
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____5223 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____5223
                                  then
                                    let uu____5224 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____5225 =
                                      let uu____5226 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____5226 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____5224 uu____5225
                                  else ());
                                 (let uu____5228 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____5228))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5231;
                FStar_Syntax_Syntax.lbunivs = uu____5232;
                FStar_Syntax_Syntax.lbtyp = uu____5233;
                FStar_Syntax_Syntax.lbeff = uu____5234;
                FStar_Syntax_Syntax.lbdef = uu____5235;_}::[]),uu____5236)
           ->
           ((let uu____5256 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5256
             then
               let uu____5257 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____5257
             else ());
            (let uu____5259 = FStar_Options.use_two_phase_tc () in
             if uu____5259
             then
               let uu____5266 =
                 check_top_level_let
                   (let uu___345_5275 = env1 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___345_5275.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___345_5275.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___345_5275.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___345_5275.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___345_5275.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___345_5275.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___345_5275.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___345_5275.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___345_5275.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___345_5275.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___345_5275.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___345_5275.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___345_5275.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___345_5275.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___345_5275.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___345_5275.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___345_5275.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___345_5275.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___345_5275.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___345_5275.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___345_5275.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___345_5275.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___345_5275.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___345_5275.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___345_5275.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___345_5275.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___345_5275.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___345_5275.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___345_5275.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___345_5275.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___345_5275.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___345_5275.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___345_5275.FStar_TypeChecker_Env.dep_graph)
                    }) top in
               match uu____5266 with
               | (lax_top,l,g) ->
                   let lax_top1 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       lax_top in
                   let uu____5286 = FStar_TypeChecker_Env.should_verify env1 in
                   (if uu____5286
                    then check_top_level_let env1 lax_top1
                    else (lax_top1, l, g))
             else check_top_level_let env1 top))
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____5295),uu____5296) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5311;
                FStar_Syntax_Syntax.lbunivs = uu____5312;
                FStar_Syntax_Syntax.lbtyp = uu____5313;
                FStar_Syntax_Syntax.lbeff = uu____5314;
                FStar_Syntax_Syntax.lbdef = uu____5315;_}::uu____5316),uu____5317)
           ->
           ((let uu____5339 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5339
             then
               let uu____5340 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____5340
             else ());
            (let uu____5342 = FStar_Options.use_two_phase_tc () in
             if uu____5342
             then
               let uu____5349 =
                 check_top_level_let_rec
                   (let uu___346_5358 = env1 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___346_5358.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___346_5358.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___346_5358.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___346_5358.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___346_5358.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___346_5358.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___346_5358.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___346_5358.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___346_5358.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___346_5358.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___346_5358.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___346_5358.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___346_5358.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___346_5358.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___346_5358.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___346_5358.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___346_5358.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___346_5358.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___346_5358.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___346_5358.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___346_5358.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___346_5358.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___346_5358.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___346_5358.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___346_5358.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___346_5358.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___346_5358.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___346_5358.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___346_5358.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___346_5358.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___346_5358.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___346_5358.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___346_5358.FStar_TypeChecker_Env.dep_graph)
                    }) top in
               match uu____5349 with
               | (lax_top,l,g) ->
                   let lax_top1 =
                     FStar_TypeChecker_Normalize.remove_uvar_solutions env1
                       lax_top in
                   let uu____5369 = FStar_TypeChecker_Env.should_verify env1 in
                   (if uu____5369
                    then check_top_level_let_rec env1 lax_top1
                    else (lax_top1, l, g))
             else check_top_level_let_rec env1 top))
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____5378),uu____5379) ->
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
        let uu____5405 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5495))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5555))::(uu____5556,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____5557))::
              (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____5630 ->
              FStar_Exn.raise
                (FStar_Errors.Error ("synth_by_tactic: bad application", rng)) in
        match uu____5405 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____5714 = FStar_TypeChecker_Env.expected_typ env in
                  (match uu____5714 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____5720 =
                         let uu____5721 =
                           let uu____5726 =
                             FStar_TypeChecker_Env.get_range env in
                           ("synth_by_tactic: need a type annotation when no expected type is present",
                             uu____5726) in
                         FStar_Errors.Error uu____5721 in
                       FStar_Exn.raise uu____5720) in
            let uu____5729 = FStar_TypeChecker_Env.clear_expected_typ env in
            (match uu____5729 with
             | (env',uu____5743) ->
                 let uu____5748 = tc_term env' typ in
                 (match uu____5748 with
                  | (typ1,uu____5762,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____5765 = tc_tactic env' tau in
                        match uu____5765 with
                        | (tau1,uu____5779,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let t =
                                if env.FStar_TypeChecker_Env.nosynth
                                then
                                  let uu____5787 =
                                    let uu____5788 =
                                      FStar_TypeChecker_Util.fvar_const env
                                        FStar_Parser_Const.magic_lid in
                                    let uu____5789 =
                                      let uu____5790 =
                                        FStar_Syntax_Syntax.as_arg
                                          FStar_Syntax_Util.exp_unit in
                                      [uu____5790] in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____5788
                                      uu____5789 in
                                  uu____5787 FStar_Pervasives_Native.None rng
                                else
                                  (let t =
                                     env.FStar_TypeChecker_Env.synth env'
                                       typ1 tau1 in
                                   (let uu____5796 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Tac") in
                                    if uu____5796
                                    then
                                      let uu____5797 =
                                        FStar_Syntax_Print.term_to_string t in
                                      FStar_Util.print1 "Got %s\n" uu____5797
                                    else ());
                                   t) in
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____5800 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng in
                               tc_term env uu____5800)))))))
and tc_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___347_5804 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___347_5804.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___347_5804.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___347_5804.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___347_5804.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___347_5804.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___347_5804.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___347_5804.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___347_5804.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___347_5804.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___347_5804.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___347_5804.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___347_5804.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___347_5804.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___347_5804.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___347_5804.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___347_5804.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___347_5804.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___347_5804.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___347_5804.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___347_5804.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___347_5804.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___347_5804.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___347_5804.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___347_5804.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___347_5804.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___347_5804.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___347_5804.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___347_5804.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___347_5804.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___347_5804.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___347_5804.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___347_5804.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___347_5804.FStar_TypeChecker_Env.dep_graph)
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
        let uu___348_5808 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___348_5808.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___348_5808.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___348_5808.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___348_5808.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___348_5808.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___348_5808.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___348_5808.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___348_5808.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___348_5808.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___348_5808.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___348_5808.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___348_5808.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___348_5808.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___348_5808.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___348_5808.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___348_5808.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___348_5808.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___348_5808.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___348_5808.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___348_5808.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___348_5808.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___348_5808.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___348_5808.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___348_5808.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___348_5808.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___348_5808.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___348_5808.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___348_5808.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___348_5808.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___348_5808.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___348_5808.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___348_5808.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___348_5808.FStar_TypeChecker_Env.dep_graph)
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
          let uu____5824 = tc_tactic env tactic in
          (match uu____5824 with
           | (tactic1,uu____5834,uu____5835) ->
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
        let uu____5874 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____5874 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____5895 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____5895
              then FStar_Util.Inl t1
              else
                (let uu____5901 =
                   let uu____5902 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____5902 in
                 FStar_Util.Inr uu____5901) in
            let is_data_ctor uu___333_5912 =
              match uu___333_5912 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____5915) -> true
              | uu____5922 -> false in
            let uu____5925 =
              (is_data_ctor dc) &&
                (let uu____5927 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____5927) in
            if uu____5925
            then
              let uu____5934 =
                let uu____5935 =
                  let uu____5940 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____5941 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____5940, uu____5941) in
                FStar_Errors.Error uu____5935 in
              FStar_Exn.raise uu____5934
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____5958 =
            let uu____5959 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____5959 in
          failwith uu____5958
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____5993 =
              let uu____5994 = FStar_Syntax_Subst.compress t1 in
              uu____5994.FStar_Syntax_Syntax.n in
            match uu____5993 with
            | FStar_Syntax_Syntax.Tm_arrow uu____5997 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____6010 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___349_6048 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___349_6048.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___349_6048.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___349_6048.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____6100 =
            let uu____6113 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____6113 with
            | FStar_Pervasives_Native.None  ->
                let uu____6128 = FStar_Syntax_Util.type_u () in
                (match uu____6128 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____6100 with
           | (t,uu____6165,g0) ->
               let uu____6179 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____6179 with
                | (e1,uu____6199,g1) ->
                    let uu____6213 =
                      let uu____6214 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____6214
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____6215 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____6213, uu____6215)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____6217 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____6230 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____6230)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____6217 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___350_6249 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___350_6249.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___350_6249.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____6252 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____6252 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____6273 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____6273
                       then FStar_Util.Inl t1
                       else
                         (let uu____6279 =
                            let uu____6280 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____6280 in
                          FStar_Util.Inr uu____6279) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6286;
             FStar_Syntax_Syntax.vars = uu____6287;_},uu____6288)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____6293 =
            let uu____6294 =
              let uu____6299 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____6299) in
            FStar_Errors.Error uu____6294 in
          FStar_Exn.raise uu____6293
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____6307 =
            let uu____6308 =
              let uu____6313 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____6313) in
            FStar_Errors.Error uu____6308 in
          FStar_Exn.raise uu____6307
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6321;
             FStar_Syntax_Syntax.vars = uu____6322;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____6331 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6331 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____6354 =
                     let uu____6355 =
                       let uu____6360 =
                         let uu____6361 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____6362 =
                           FStar_Util.string_of_int (FStar_List.length us1) in
                         let uu____6363 =
                           FStar_Util.string_of_int (FStar_List.length us') in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____6361 uu____6362 uu____6363 in
                       let uu____6364 = FStar_TypeChecker_Env.get_range env1 in
                       (uu____6360, uu____6364) in
                     FStar_Errors.Error uu____6355 in
                   FStar_Exn.raise uu____6354)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____6380 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6384 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6384 us1 in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6386 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6386 with
           | ((us,t),range) ->
               ((let uu____6409 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____6409
                 then
                   let uu____6410 =
                     let uu____6411 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____6411 in
                   let uu____6412 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____6413 = FStar_Range.string_of_range range in
                   let uu____6414 = FStar_Range.string_of_use_range range in
                   let uu____6415 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____6410 uu____6412 uu____6413 uu____6414 uu____6415
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6420 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6420 us in
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
          let uu____6444 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6444 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____6458 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____6458 with
                | (env2,uu____6472) ->
                    let uu____6477 = tc_binders env2 bs1 in
                    (match uu____6477 with
                     | (bs2,env3,g,us) ->
                         let uu____6496 = tc_comp env3 c1 in
                         (match uu____6496 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___351_6515 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___351_6515.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___351_6515.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____6524 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____6524 in
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
          let uu____6543 =
            let uu____6548 =
              let uu____6549 = FStar_Syntax_Syntax.mk_binder x in
              [uu____6549] in
            FStar_Syntax_Subst.open_term uu____6548 phi in
          (match uu____6543 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____6559 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____6559 with
                | (env2,uu____6573) ->
                    let uu____6578 =
                      let uu____6591 = FStar_List.hd x1 in
                      tc_binder env2 uu____6591 in
                    (match uu____6578 with
                     | (x2,env3,f1,u) ->
                         ((let uu____6619 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____6619
                           then
                             let uu____6620 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____6621 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____6622 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____6620 uu____6621 uu____6622
                           else ());
                          (let uu____6624 = FStar_Syntax_Util.type_u () in
                           match uu____6624 with
                           | (t_phi,uu____6636) ->
                               let uu____6637 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____6637 with
                                | (phi2,uu____6651,f2) ->
                                    let e1 =
                                      let uu___352_6656 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___352_6656.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___352_6656.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____6663 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____6663 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____6676) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____6699 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____6699
            then
              let uu____6700 =
                FStar_Syntax_Print.term_to_string
                  (let uu___353_6703 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___353_6703.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___353_6703.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____6700
            else ());
           (let uu____6709 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____6709 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____6722 ->
          let uu____6723 =
            let uu____6724 = FStar_Syntax_Print.term_to_string top in
            let uu____6725 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____6724
              uu____6725 in
          failwith uu____6723
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
      | FStar_Const.Const_bool uu____6734 -> FStar_Syntax_Util.t_bool
      | FStar_Const.Const_int (uu____6735,FStar_Pervasives_Native.None ) ->
          FStar_Syntax_Syntax.t_int
      | FStar_Const.Const_int
          (uu____6746,FStar_Pervasives_Native.Some uu____6747) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____6762 -> FStar_Syntax_Syntax.t_string
      | FStar_Const.Const_float uu____6767 -> FStar_Syntax_Syntax.t_float
      | FStar_Const.Const_char uu____6768 -> FStar_Syntax_Syntax.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____6769 -> FStar_Syntax_Syntax.t_range
      | FStar_Const.Const_range_of  ->
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
      | FStar_Const.Const_set_range_of  ->
          let uu____6778 =
            let uu____6779 =
              let uu____6784 =
                let uu____6785 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6785 in
              (uu____6784, r) in
            FStar_Errors.Error uu____6779 in
          FStar_Exn.raise uu____6778
      | FStar_Const.Const_reify  ->
          let uu____6786 =
            let uu____6787 =
              let uu____6792 =
                let uu____6793 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6793 in
              (uu____6792, r) in
            FStar_Errors.Error uu____6787 in
          FStar_Exn.raise uu____6786
      | FStar_Const.Const_reflect uu____6794 ->
          let uu____6795 =
            let uu____6796 =
              let uu____6801 =
                let uu____6802 = FStar_Parser_Const.const_to_string c in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____6802 in
              (uu____6801, r) in
            FStar_Errors.Error uu____6796 in
          FStar_Exn.raise uu____6795
      | uu____6803 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____6820) ->
          let uu____6829 = FStar_Syntax_Util.type_u () in
          (match uu____6829 with
           | (k,u) ->
               let uu____6842 = tc_check_tot_or_gtot_term env t k in
               (match uu____6842 with
                | (t1,uu____6856,g) ->
                    let uu____6858 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____6858, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____6860) ->
          let uu____6869 = FStar_Syntax_Util.type_u () in
          (match uu____6869 with
           | (k,u) ->
               let uu____6882 = tc_check_tot_or_gtot_term env t k in
               (match uu____6882 with
                | (t1,uu____6896,g) ->
                    let uu____6898 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____6898, u, g)))
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
            let uu____6906 =
              let uu____6907 =
                let uu____6908 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____6908 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____6907 in
            uu____6906 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____6911 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____6911 with
           | (tc1,uu____6925,f) ->
               let uu____6927 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____6927 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____6971 =
                        let uu____6972 = FStar_Syntax_Subst.compress head3 in
                        uu____6972.FStar_Syntax_Syntax.n in
                      match uu____6971 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____6975,us) -> us
                      | uu____6981 -> [] in
                    let uu____6982 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____6982 with
                     | (uu____7003,args1) ->
                         let uu____7025 =
                           let uu____7044 = FStar_List.hd args1 in
                           let uu____7057 = FStar_List.tl args1 in
                           (uu____7044, uu____7057) in
                         (match uu____7025 with
                          | (res,args2) ->
                              let uu____7122 =
                                let uu____7131 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___334_7159  ->
                                          match uu___334_7159 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____7167 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____7167 with
                                               | (env1,uu____7179) ->
                                                   let uu____7184 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____7184 with
                                                    | (e1,uu____7196,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____7131
                                  FStar_List.unzip in
                              (match uu____7122 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___354_7235 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___354_7235.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___354_7235.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____7239 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____7239 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____7243 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____7243))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____7251 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____7252 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____7262 = aux u3 in FStar_Syntax_Syntax.U_succ uu____7262
        | FStar_Syntax_Syntax.U_max us ->
            let uu____7266 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____7266
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____7271 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____7271 FStar_Pervasives_Native.snd
         | uu____7280 -> aux u)
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
            let uu____7304 =
              let uu____7305 =
                let uu____7310 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____7310, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____7305 in
            FStar_Exn.raise uu____7304 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____7400 bs2 bs_expected1 =
              match uu____7400 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____7568)) ->
                             let uu____7573 =
                               let uu____7574 =
                                 let uu____7579 =
                                   let uu____7580 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____7580 in
                                 let uu____7581 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____7579, uu____7581) in
                               FStar_Errors.Error uu____7574 in
                             FStar_Exn.raise uu____7573
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____7582),FStar_Pervasives_Native.None ) ->
                             let uu____7587 =
                               let uu____7588 =
                                 let uu____7593 =
                                   let uu____7594 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____7594 in
                                 let uu____7595 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____7593, uu____7595) in
                               FStar_Errors.Error uu____7588 in
                             FStar_Exn.raise uu____7587
                         | uu____7596 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____7602 =
                           let uu____7607 =
                             let uu____7608 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____7608.FStar_Syntax_Syntax.n in
                           match uu____7607 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____7615 ->
                               ((let uu____7617 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____7617
                                 then
                                   let uu____7618 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____7618
                                 else ());
                                (let uu____7620 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____7620 with
                                 | (t,uu____7632,g1) ->
                                     let g2 =
                                       let uu____7635 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____7636 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____7635
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____7636 in
                                     let g3 =
                                       let uu____7638 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____7638 in
                                     (t, g3))) in
                         match uu____7602 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___355_7666 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___355_7666.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___355_7666.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____7679 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____7679 in
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
                  | uu____7825 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____7832 = tc_binders env1 bs in
                  match uu____7832 with
                  | (bs1,envbody,g,uu____7862) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____7906 =
                    let uu____7907 = FStar_Syntax_Subst.compress t2 in
                    uu____7907.FStar_Syntax_Syntax.n in
                  match uu____7906 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____7930 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____7952 -> failwith "Impossible");
                       (let uu____7959 = tc_binders env1 bs in
                        match uu____7959 with
                        | (bs1,envbody,g,uu____7991) ->
                            let uu____7992 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____7992 with
                             | (envbody1,uu____8020) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____8031;
                         FStar_Syntax_Syntax.pos = uu____8032;
                         FStar_Syntax_Syntax.vars = uu____8033;_},uu____8034)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8076 -> failwith "Impossible");
                       (let uu____8083 = tc_binders env1 bs in
                        match uu____8083 with
                        | (bs1,envbody,g,uu____8115) ->
                            let uu____8116 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____8116 with
                             | (envbody1,uu____8144) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____8156) ->
                      let uu____8161 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____8161 with
                       | (uu____8202,bs1,bs',copt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____8245 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____8245 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____8345 c_expected2 =
                               match uu____8345 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____8460 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____8460)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____8491 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____8491 in
                                        let uu____8492 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____8492)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        let uu____8517 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c) in
                                        if uu____8517
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
                                               let uu____8565 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____8565 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____8586 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____8586 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____8634 =
                                                           let uu____8665 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____8665,
                                                             subst2) in
                                                         handle_more
                                                           uu____8634
                                                           c_expected4))
                                           | uu____8682 ->
                                               let uu____8683 =
                                                 let uu____8684 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____8684 in
                                               fail uu____8683 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____8714 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____8714 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___356_8773 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___356_8773.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___356_8773.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___356_8773.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___356_8773.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___356_8773.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___356_8773.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___356_8773.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___356_8773.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___356_8773.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___356_8773.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___356_8773.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___356_8773.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___356_8773.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___356_8773.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___356_8773.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___356_8773.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___356_8773.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___356_8773.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___356_8773.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___356_8773.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___356_8773.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___356_8773.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___356_8773.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___356_8773.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___356_8773.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___356_8773.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___356_8773.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___356_8773.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___356_8773.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___356_8773.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___356_8773.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___356_8773.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___356_8773.FStar_TypeChecker_Env.dep_graph)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____8812  ->
                                     fun uu____8813  ->
                                       match (uu____8812, uu____8813) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____8858 =
                                             let uu____8865 =
                                               let uu____8866 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____8866
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____8865 t3 in
                                           (match uu____8858 with
                                            | (t4,uu____8888,uu____8889) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____8899 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___357_8902
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___357_8902.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___357_8902.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____8899 ::
                                                        letrec_binders
                                                  | uu____8903 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____8908 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____8908 with
                            | (envbody,bs1,g,c) ->
                                let uu____8959 =
                                  let uu____8966 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____8966
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____8959 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body1, g))))
                  | uu____9015 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____9036 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____9036
                      else
                        (let uu____9038 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1 in
                         match uu____9038 with
                         | (uu____9077,bs1,uu____9079,c_opt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____9099 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____9099 with
          | (env1,topt) ->
              ((let uu____9119 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____9119
                then
                  let uu____9120 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____9120
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____9124 = expected_function_typ1 env1 topt body in
                match uu____9124 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let uu____9164 =
                      let should_check_expected_effect =
                        let uu____9172 =
                          let uu____9179 =
                            let uu____9180 =
                              FStar_Syntax_Subst.compress body1 in
                            uu____9180.FStar_Syntax_Syntax.n in
                          (c_opt, uu____9179) in
                        match uu____9172 with
                        | (FStar_Pervasives_Native.None
                           ,FStar_Syntax_Syntax.Tm_ascribed
                           (uu____9185,(FStar_Util.Inr expected_c,uu____9187),uu____9188))
                            -> false
                        | uu____9237 -> true in
                      let uu____9244 =
                        tc_term
                          (let uu___358_9253 = envbody in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___358_9253.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___358_9253.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___358_9253.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___358_9253.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___358_9253.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___358_9253.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___358_9253.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___358_9253.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___358_9253.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___358_9253.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___358_9253.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___358_9253.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___358_9253.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = false;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___358_9253.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq = use_eq;
                             FStar_TypeChecker_Env.is_iface =
                               (uu___358_9253.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___358_9253.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___358_9253.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___358_9253.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___358_9253.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___358_9253.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___358_9253.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___358_9253.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___358_9253.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___358_9253.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qname_and_index =
                               (uu___358_9253.FStar_TypeChecker_Env.qname_and_index);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___358_9253.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth =
                               (uu___358_9253.FStar_TypeChecker_Env.synth);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___358_9253.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___358_9253.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___358_9253.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___358_9253.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___358_9253.FStar_TypeChecker_Env.dep_graph)
                           }) body1 in
                      match uu____9244 with
                      | (body2,cbody,guard_body) ->
                          let guard_body1 =
                            FStar_TypeChecker_Rel.solve_deferred_constraints
                              envbody guard_body in
                          if should_check_expected_effect
                          then
                            let uu____9270 =
                              let uu____9277 =
                                let uu____9282 =
                                  cbody.FStar_Syntax_Syntax.comp () in
                                (body2, uu____9282) in
                              check_expected_effect
                                (let uu___359_9289 = envbody in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___359_9289.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___359_9289.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___359_9289.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___359_9289.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___359_9289.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___359_9289.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___359_9289.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___359_9289.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___359_9289.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___359_9289.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___359_9289.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___359_9289.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___359_9289.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___359_9289.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___359_9289.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___359_9289.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___359_9289.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___359_9289.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___359_9289.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___359_9289.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___359_9289.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___359_9289.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___359_9289.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___359_9289.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___359_9289.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___359_9289.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___359_9289.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___359_9289.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___359_9289.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___359_9289.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___359_9289.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___359_9289.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___359_9289.FStar_TypeChecker_Env.dep_graph)
                                 }) c_opt uu____9277 in
                            (match uu____9270 with
                             | (body3,cbody1,guard) ->
                                 let uu____9299 =
                                   FStar_TypeChecker_Rel.conj_guard
                                     guard_body1 guard in
                                 (body3, cbody1, uu____9299))
                          else
                            (let uu____9301 =
                               cbody.FStar_Syntax_Syntax.comp () in
                             (body2, uu____9301, guard_body1)) in
                    (match uu____9164 with
                     | (body2,cbody,guard) ->
                         let guard1 =
                           let uu____9316 =
                             env1.FStar_TypeChecker_Env.top_level ||
                               (let uu____9318 =
                                  FStar_TypeChecker_Env.should_verify env1 in
                                Prims.op_Negation uu____9318) in
                           if uu____9316
                           then
                             let uu____9319 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             FStar_TypeChecker_Rel.discharge_guard envbody
                               uu____9319
                           else
                             (let guard1 =
                                let uu____9322 =
                                  FStar_TypeChecker_Rel.conj_guard g guard in
                                FStar_TypeChecker_Rel.close_guard env1
                                  (FStar_List.append bs1 letrec_binders)
                                  uu____9322 in
                              guard1) in
                         let tfun_computed =
                           FStar_Syntax_Util.arrow bs1 cbody in
                         let e =
                           FStar_Syntax_Util.abs bs1 body2
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp
                                   (FStar_Util.dflt cbody c_opt))) in
                         let uu____9331 =
                           match tfun_opt with
                           | FStar_Pervasives_Native.Some t ->
                               let t1 = FStar_Syntax_Subst.compress t in
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_arrow uu____9352 ->
                                    (e, t1, guard1)
                                | uu____9365 ->
                                    let uu____9366 =
                                      FStar_TypeChecker_Util.check_and_ascribe
                                        env1 e tfun_computed t1 in
                                    (match uu____9366 with
                                     | (e1,guard') ->
                                         let uu____9379 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 guard' in
                                         (e1, t1, uu____9379)))
                           | FStar_Pervasives_Native.None  ->
                               (e, tfun_computed, guard1) in
                         (match uu____9331 with
                          | (e1,tfun,guard2) ->
                              let c =
                                if env1.FStar_TypeChecker_Env.top_level
                                then FStar_Syntax_Syntax.mk_Total tfun
                                else
                                  FStar_TypeChecker_Util.return_value env1
                                    tfun e1 in
                              let uu____9393 =
                                FStar_TypeChecker_Util.strengthen_precondition
                                  FStar_Pervasives_Native.None env1 e1
                                  (FStar_Syntax_Util.lcomp_of_comp c) guard2 in
                              (match uu____9393 with
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
              (let uu____9442 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____9442
               then
                 let uu____9443 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____9444 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____9443
                   uu____9444
               else ());
              (let monadic_application uu____9501 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____9501 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___360_9560 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___360_9560.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___360_9560.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___360_9560.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____9561 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
                       | uu____9576 ->
                           let g =
                             let uu____9584 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____9584
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____9585 =
                             let uu____9586 =
                               let uu____9589 =
                                 let uu____9590 =
                                   let uu____9591 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____9591 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____9590 in
                               FStar_Syntax_Syntax.mk_Total uu____9589 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____9586 in
                           (uu____9585, g) in
                     (match uu____9561 with
                      | (cres2,guard1) ->
                          ((let uu____9605 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____9605
                            then
                              let uu____9606 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____9606
                            else ());
                           (let cres3 =
                              let uu____9609 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____9609
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
                                   fun uu____9643  ->
                                     match uu____9643 with
                                     | ((e,q),x,c) ->
                                         let uu____9676 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____9676
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
                              let uu____9688 =
                                let uu____9689 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____9689.FStar_Syntax_Syntax.n in
                              match uu____9688 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____9693 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____9714  ->
                                         match uu____9714 with
                                         | (arg,uu____9728,uu____9729) -> arg
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
                                (let uu____9739 =
                                   let map_fun uu____9801 =
                                     match uu____9801 with
                                     | ((e,q),uu____9836,c) ->
                                         let uu____9846 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____9846
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
                                            let uu____9896 =
                                              let uu____9901 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____9901, q) in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____9896)) in
                                   let uu____9930 =
                                     let uu____9955 =
                                       let uu____9978 =
                                         let uu____9993 =
                                           let uu____10002 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____10002,
                                             FStar_Pervasives_Native.None,
                                             chead1) in
                                         uu____9993 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____9978 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____9955 in
                                   match uu____9930 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____10175 =
                                         let uu____10176 =
                                           FStar_List.hd reverse_args in
                                         FStar_Pervasives_Native.fst
                                           uu____10176 in
                                       let uu____10185 =
                                         let uu____10192 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____10192 in
                                       (lifted_args, uu____10175,
                                         uu____10185) in
                                 match uu____9739 with
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
                                     let bind_lifted_args e uu___335_10295 =
                                       match uu___335_10295 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____10350 =
                                               let uu____10353 =
                                                 let uu____10354 =
                                                   let uu____10367 =
                                                     let uu____10368 =
                                                       let uu____10369 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____10369] in
                                                     FStar_Syntax_Subst.close
                                                       uu____10368 e in
                                                   ((false, [lb]),
                                                     uu____10367) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____10354 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10353 in
                                             uu____10350
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
                            let uu____10399 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp1
                                guard1 in
                            match uu____10399 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____10490 bs args1 =
                 match uu____10490 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____10637))::rest,
                         (uu____10639,FStar_Pervasives_Native.None )::uu____10640)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t in
                          let uu____10701 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____10701 with
                           | (varg,uu____10721,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____10743 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____10743) in
                               let uu____10744 =
                                 let uu____10779 =
                                   let uu____10794 =
                                     let uu____10807 =
                                       let uu____10808 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____10808
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____10807) in
                                   uu____10794 :: outargs in
                                 let uu____10827 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____10779, (arg :: arg_rets),
                                   uu____10827, fvs) in
                               tc_args head_info uu____10744 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____10929),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____10930)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____10943 ->
                                FStar_Exn.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___361_10954 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___361_10954.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___361_10954.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____10956 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____10956
                             then
                               let uu____10957 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____10957
                             else ());
                            (let targ1 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___362_10962 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___362_10962.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___362_10962.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___362_10962.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___362_10962.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___362_10962.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___362_10962.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___362_10962.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___362_10962.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___362_10962.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___362_10962.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___362_10962.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___362_10962.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___362_10962.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___362_10962.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___362_10962.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___362_10962.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___362_10962.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___362_10962.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___362_10962.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___362_10962.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___362_10962.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___362_10962.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___362_10962.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___362_10962.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___362_10962.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___362_10962.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___362_10962.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___362_10962.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___362_10962.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___362_10962.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___362_10962.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___362_10962.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___362_10962.FStar_TypeChecker_Env.dep_graph)
                               } in
                             (let uu____10964 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____10964
                              then
                                let uu____10965 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____10966 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____10967 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____10965 uu____10966 uu____10967
                              else ());
                             (let uu____10969 = tc_term env2 e in
                              match uu____10969 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____10996 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____10996 in
                                  let uu____10997 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____10997
                                  then
                                    let subst2 =
                                      let uu____11005 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____11005
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
                      | (uu____11099,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____11135) ->
                          let uu____11186 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____11186 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____11220 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____11220
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____11245 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____11245 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____11268 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____11268
                                            then
                                              FStar_Errors.warn
                                                tres1.FStar_Syntax_Syntax.pos
                                                "Potentially redundant explicit currying of a function type"
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____11310 when Prims.op_Negation norm1
                                     ->
                                     let uu____11311 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____11311
                                 | uu____11312 ->
                                     let uu____11313 =
                                       let uu____11314 =
                                         let uu____11319 =
                                           let uu____11320 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____11321 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____11320 uu____11321 in
                                         let uu____11328 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____11319, uu____11328) in
                                       FStar_Errors.Error uu____11314 in
                                     FStar_Exn.raise uu____11313 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____11347 =
                   let uu____11348 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____11348.FStar_Syntax_Syntax.n in
                 match uu____11347 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____11359 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____11460 = tc_term env1 e in
                           (match uu____11460 with
                            | (e1,c,g_e) ->
                                let uu____11482 = tc_args1 env1 tl1 in
                                (match uu____11482 with
                                 | (args2,comps,g_rest) ->
                                     let uu____11522 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____11522))) in
                     let uu____11543 = tc_args1 env args in
                     (match uu____11543 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____11580 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____11618  ->
                                      match uu____11618 with
                                      | (uu____11631,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____11580 in
                          let ml_or_tot t r1 =
                            let uu____11648 = FStar_Options.ml_ish () in
                            if uu____11648
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____11651 =
                              let uu____11654 =
                                let uu____11655 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____11655
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____11654 in
                            ml_or_tot uu____11651 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____11668 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____11668
                            then
                              let uu____11669 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____11670 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____11671 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____11669 uu____11670 uu____11671
                            else ());
                           (let uu____11674 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____11674);
                           (let comp =
                              let uu____11676 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____11687  ->
                                   fun out  ->
                                     match uu____11687 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____11676 in
                            let uu____11701 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____11704 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____11701, comp, uu____11704))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____11707;
                        FStar_Syntax_Syntax.pos = uu____11708;
                        FStar_Syntax_Syntax.vars = uu____11709;_},uu____11710)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____11831 = tc_term env1 e in
                           (match uu____11831 with
                            | (e1,c,g_e) ->
                                let uu____11853 = tc_args1 env1 tl1 in
                                (match uu____11853 with
                                 | (args2,comps,g_rest) ->
                                     let uu____11893 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____11893))) in
                     let uu____11914 = tc_args1 env args in
                     (match uu____11914 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____11951 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____11989  ->
                                      match uu____11989 with
                                      | (uu____12002,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____11951 in
                          let ml_or_tot t r1 =
                            let uu____12019 = FStar_Options.ml_ish () in
                            if uu____12019
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____12022 =
                              let uu____12025 =
                                let uu____12026 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____12026
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____12025 in
                            ml_or_tot uu____12022 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____12039 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____12039
                            then
                              let uu____12040 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____12041 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____12042 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____12040 uu____12041 uu____12042
                            else ());
                           (let uu____12045 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____12045);
                           (let comp =
                              let uu____12047 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____12058  ->
                                   fun out  ->
                                     match uu____12058 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____12047 in
                            let uu____12072 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____12075 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____12072, comp, uu____12075))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____12096 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____12096 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____12161) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____12167,uu____12168) -> check_function_app t
                 | uu____12209 ->
                     let uu____12210 =
                       let uu____12211 =
                         let uu____12216 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____12216, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____12211 in
                     FStar_Exn.raise uu____12210 in
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
                  let uu____12286 =
                    FStar_List.fold_left2
                      (fun uu____12329  ->
                         fun uu____12330  ->
                           fun uu____12331  ->
                             match (uu____12329, uu____12330, uu____12331)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Exn.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____12399 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____12399 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____12417 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____12417 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____12421 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____12421)
                                              &&
                                              (let uu____12423 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____12423)) in
                                       let uu____12424 =
                                         let uu____12433 =
                                           let uu____12442 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____12442] in
                                         FStar_List.append seen uu____12433 in
                                       let uu____12449 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____12424, uu____12449, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____12286 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r in
                       let c1 =
                         if ghost
                         then
                           let uu____12485 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____12485
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____12487 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____12487 with | (c2,g) -> (e, c2, g)))
              | uu____12504 ->
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
        let uu____12538 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____12538 with
        | (pattern,when_clause,branch_exp) ->
            let uu____12574 = branch1 in
            (match uu____12574 with
             | (cpat,uu____12606,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let tc_annot env1 t =
                     let uu____12665 = FStar_Syntax_Util.type_u () in
                     match uu____12665 with
                     | (tu,u) ->
                         let uu____12672 =
                           tc_check_tot_or_gtot_term env1 t tu in
                         (match uu____12672 with
                          | (t1,uu____12680,g) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env1
                                 g;
                               t1)) in
                   let uu____12683 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0
                       tc_annot in
                   match uu____12683 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____12712 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____12712
                         then
                           let uu____12713 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____12714 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____12713 uu____12714
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____12717 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____12717 with
                         | (env1,uu____12737) ->
                             let env11 =
                               let uu___363_12743 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___363_12743.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___363_12743.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___363_12743.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___363_12743.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___363_12743.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___363_12743.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___363_12743.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___363_12743.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___363_12743.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___363_12743.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___363_12743.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___363_12743.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___363_12743.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___363_12743.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___363_12743.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___363_12743.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___363_12743.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___363_12743.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___363_12743.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___363_12743.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___363_12743.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___363_12743.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___363_12743.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___363_12743.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___363_12743.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___363_12743.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___363_12743.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___363_12743.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___363_12743.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___363_12743.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___363_12743.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___363_12743.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___363_12743.FStar_TypeChecker_Env.dep_graph)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____12746 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____12746
                               then
                                 let uu____12747 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____12748 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____12747 uu____12748
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t in
                               let uu____12751 =
                                 tc_tot_or_gtot_term env12 exp in
                               match uu____12751 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___364_12774 = g in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___364_12774.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___364_12774.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___364_12774.FStar_TypeChecker_Env.implicits)
                                     } in
                                   let uu____12775 =
                                     let uu____12776 =
                                       FStar_TypeChecker_Rel.teq_nosmt env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t in
                                     if uu____12776
                                     then
                                       let env13 =
                                         FStar_TypeChecker_Env.set_range
                                           env12 exp1.FStar_Syntax_Syntax.pos in
                                       let uu____12778 =
                                         FStar_TypeChecker_Rel.discharge_guard_no_smt
                                           env13 g1 in
                                       FStar_All.pipe_right uu____12778
                                         FStar_TypeChecker_Rel.resolve_implicits
                                     else
                                       (let uu____12780 =
                                          let uu____12781 =
                                            let uu____12786 =
                                              let uu____12787 =
                                                FStar_Syntax_Print.term_to_string
                                                  lc.FStar_Syntax_Syntax.res_typ in
                                              let uu____12788 =
                                                FStar_Syntax_Print.term_to_string
                                                  expected_pat_t in
                                              FStar_Util.format2
                                                "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                                uu____12787 uu____12788 in
                                            (uu____12786,
                                              (exp1.FStar_Syntax_Syntax.pos)) in
                                          FStar_Errors.Error uu____12781 in
                                        FStar_Exn.raise uu____12780) in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1 in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____12805 =
                                       let uu____12806 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____12806 in
                                     if uu____12805
                                     then
                                       let unresolved =
                                         let uu____12818 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____12818
                                           FStar_Util.set_elements in
                                       let uu____12845 =
                                         let uu____12846 =
                                           let uu____12851 =
                                             let uu____12852 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____12853 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____12854 =
                                               let uu____12855 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____12873  ->
                                                         match uu____12873
                                                         with
                                                         | (u,uu____12879) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____12855
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____12852 uu____12853
                                               uu____12854 in
                                           (uu____12851,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____12846 in
                                       FStar_Exn.raise uu____12845
                                     else ());
                                    (let uu____12884 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____12884
                                     then
                                       let uu____12885 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____12885
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____12894 =
                   let uu____12901 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____12901
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____12894 with
                  | (scrutinee_env,uu____12925) ->
                      let uu____12930 = tc_pat true pat_t pattern in
                      (match uu____12930 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____12968 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____12990 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____12990
                                 then
                                   FStar_Exn.raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____13004 =
                                      let uu____13011 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool in
                                      tc_term uu____13011 e in
                                    match uu____13004 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g)) in
                           (match uu____12968 with
                            | (when_clause1,g_when) ->
                                let uu____13045 = tc_term pat_env branch_exp in
                                (match uu____13045 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some w ->
                                           let uu____13077 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_40  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_40) uu____13077 in
                                     let uu____13080 =
                                       let eqs =
                                         let uu____13090 =
                                           let uu____13091 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____13091 in
                                         if uu____13090
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____13098 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____13115 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____13116 ->
                                                FStar_Pervasives_Native.None
                                            | uu____13117 ->
                                                let uu____13118 =
                                                  let uu____13119 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____13119 pat_t
                                                    scrutinee_tm e in
                                                FStar_Pervasives_Native.Some
                                                  uu____13118) in
                                       let uu____13120 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch in
                                       match uu____13120 with
                                       | (c1,g_branch1) ->
                                           let uu____13135 =
                                             match (eqs, when_condition) with
                                             | uu____13148 when
                                                 let uu____13157 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation
                                                   uu____13157
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
                                                 let uu____13169 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____13170 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____13169, uu____13170)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____13179 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____13179 in
                                                 let uu____13180 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____13181 =
                                                   let uu____13182 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____13182 g_when in
                                                 (uu____13180, uu____13181)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____13190 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____13190, g_when) in
                                           (match uu____13135 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____13202 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____13203 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____13202, uu____13203,
                                                  g_branch1)) in
                                     (match uu____13080 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____13224 =
                                              let uu____13225 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____13225 in
                                            if uu____13224
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____13255 =
                                                     let uu____13256 =
                                                       let uu____13257 =
                                                         let uu____13260 =
                                                           let uu____13267 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____13267 in
                                                         FStar_Pervasives_Native.snd
                                                           uu____13260 in
                                                       FStar_List.length
                                                         uu____13257 in
                                                     uu____13256 >
                                                       (Prims.parse_int "1") in
                                                   if uu____13255
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____13273 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____13273 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____13294 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None in
                                                         let disc1 =
                                                           let uu____13309 =
                                                             let uu____13310
                                                               =
                                                               let uu____13311
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____13311] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____13310 in
                                                           uu____13309
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____13314 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool in
                                                         [uu____13314]
                                                   else [] in
                                                 let fail uu____13319 =
                                                   let uu____13320 =
                                                     let uu____13321 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____13322 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____13323 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____13321
                                                       uu____13322
                                                       uu____13323 in
                                                   failwith uu____13320 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____13334) ->
                                                       head_constructor t1
                                                   | uu____13339 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____13341 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____13341
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____13344 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____13361;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____13362;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____13363;_},uu____13364)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____13401 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____13403 =
                                                       let uu____13404 =
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____13404
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____13403]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____13405 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____13413 =
                                                       let uu____13414 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____13414 in
                                                     if uu____13413
                                                     then []
                                                     else
                                                       (let uu____13418 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13418)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____13421 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____13423 =
                                                       let uu____13424 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____13424 in
                                                     if uu____13423
                                                     then []
                                                     else
                                                       (let uu____13428 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13428)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____13454 =
                                                       let uu____13455 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____13455 in
                                                     if uu____13454
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____13462 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____13494
                                                                     ->
                                                                    match uu____13494
                                                                    with
                                                                    | 
                                                                    (ei,uu____13504)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____13510
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____13510
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____13531
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____13545
                                                                    =
                                                                    let uu____13546
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____13547
                                                                    =
                                                                    let uu____13548
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____13548] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____13546
                                                                    uu____13547 in
                                                                    uu____13545
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____13462
                                                            FStar_List.flatten in
                                                        let uu____13557 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____13557
                                                          sub_term_guards)
                                                 | uu____13560 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____13572 =
                                                   let uu____13573 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____13573 in
                                                 if uu____13572
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____13576 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____13576 in
                                                    let uu____13581 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____13581 with
                                                    | (k,uu____13587) ->
                                                        let uu____13588 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____13588
                                                         with
                                                         | (t1,uu____13596,uu____13597)
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
                                          ((let uu____13603 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____13603
                                            then
                                              let uu____13604 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____13604
                                            else ());
                                           (let uu____13606 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____13606, branch_guard, c1,
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
          let uu____13632 = check_let_bound_def true env1 lb in
          (match uu____13632 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____13654 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____13671 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____13671, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____13674 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____13674
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____13678 =
                      let uu____13691 =
                        let uu____13706 =
                          let uu____13715 =
                            let uu____13728 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____13728) in
                          [uu____13715] in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____13706 in
                      FStar_List.hd uu____13691 in
                    match uu____13678 with
                    | (uu____13781,univs1,e11,c11,gvs) ->
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
               (match uu____13654 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____13804 =
                      let uu____13811 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____13811
                      then
                        let uu____13818 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____13818 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____13841 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____13841
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____13842 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____13842, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____13852 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____13852
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm] env1) in
                          let e21 =
                            let uu____13860 =
                              FStar_Syntax_Util.is_pure_comp c in
                            if uu____13860
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
                    (match uu____13804 with
                     | (e21,c12) ->
                         let cres =
                           FStar_TypeChecker_Env.null_wp_for_eff env1
                             (FStar_Syntax_Util.comp_effect_name c12)
                             FStar_Syntax_Syntax.U_zero
                             FStar_Syntax_Syntax.t_unit in
                         let lb1 =
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             lb.FStar_Syntax_Syntax.lbname univ_vars2
                             (FStar_Syntax_Util.comp_result c12)
                             (FStar_Syntax_Util.comp_effect_name c12) e11 in
                         let uu____13882 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         (uu____13882,
                           (FStar_Syntax_Util.lcomp_of_comp cres),
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____13897 -> failwith "Impossible"
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
            let uu___365_13928 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___365_13928.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___365_13928.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___365_13928.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___365_13928.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___365_13928.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___365_13928.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___365_13928.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___365_13928.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___365_13928.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___365_13928.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___365_13928.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___365_13928.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___365_13928.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___365_13928.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___365_13928.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___365_13928.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___365_13928.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___365_13928.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___365_13928.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___365_13928.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___365_13928.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___365_13928.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___365_13928.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___365_13928.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___365_13928.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___365_13928.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___365_13928.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___365_13928.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___365_13928.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___365_13928.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___365_13928.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___365_13928.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___365_13928.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____13929 =
            let uu____13940 =
              let uu____13941 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____13941 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____13940 lb in
          (match uu____13929 with
           | (e1,uu____13963,c1,g1,annotated) ->
               let x =
                 let uu___366_13968 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___366_13968.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___366_13968.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____13969 =
                 let uu____13974 =
                   let uu____13975 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____13975] in
                 FStar_Syntax_Subst.open_term uu____13974 e2 in
               (match uu____13969 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = FStar_Pervasives_Native.fst xbinder in
                    let uu____13994 =
                      let uu____14001 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____14001 e21 in
                    (match uu____13994 with
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
                           let uu____14020 =
                             let uu____14023 =
                               let uu____14024 =
                                 let uu____14037 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____14037) in
                               FStar_Syntax_Syntax.Tm_let uu____14024 in
                             FStar_Syntax_Syntax.mk uu____14023 in
                           uu____14020 FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____14051 =
                             let uu____14052 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____14053 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____14052
                               c1.FStar_Syntax_Syntax.res_typ uu____14053 e11 in
                           FStar_All.pipe_left
                             (fun _0_41  ->
                                FStar_TypeChecker_Common.NonTrivial _0_41)
                             uu____14051 in
                         let g21 =
                           let uu____14055 =
                             let uu____14056 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____14056 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____14055 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____14058 =
                           let uu____14059 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____14059 in
                         if uu____14058
                         then
                           let tt =
                             let uu____14069 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____14069
                               FStar_Option.get in
                           ((let uu____14075 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____14075
                             then
                               let uu____14076 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____14077 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____14076 uu____14077
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape FStar_Pervasives_Native.None
                                env2 [x1] cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____14082 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____14082
                             then
                               let uu____14083 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____14084 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____14083 uu____14084
                             else ());
                            (e4,
                              ((let uu___367_14087 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___367_14087.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___367_14087.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___367_14087.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____14088 -> failwith "Impossible"
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
          let uu____14120 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____14120 with
           | (lbs1,e21) ->
               let uu____14139 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____14139 with
                | (env0,topt) ->
                    let uu____14158 = build_let_rec_env true env0 lbs1 in
                    (match uu____14158 with
                     | (lbs2,rec_env) ->
                         let uu____14177 = check_let_recs rec_env lbs2 in
                         (match uu____14177 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____14197 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____14197
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____14203 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____14203
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
                                              lb.FStar_Syntax_Syntax.lbname
                                              lb.FStar_Syntax_Syntax.lbunivs
                                              lb.FStar_Syntax_Syntax.lbtyp
                                              lb.FStar_Syntax_Syntax.lbeff
                                              lbdef))
                                else
                                  (let ecs =
                                     let uu____14252 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____14292 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____14292))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____14252 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____14339  ->
                                           match uu____14339 with
                                           | (x,uvs,e,c,gvs) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____14380 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____14380 in
                              let uu____14385 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                              (match uu____14385 with
                               | (lbs5,e22) ->
                                   ((let uu____14405 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1 in
                                     FStar_All.pipe_right uu____14405
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____14406 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     (uu____14406, cres,
                                       FStar_TypeChecker_Rel.trivial_guard))))))))
      | uu____14419 -> failwith "Impossible"
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
          let uu____14451 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____14451 with
           | (lbs1,e21) ->
               let uu____14470 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____14470 with
                | (env0,topt) ->
                    let uu____14489 = build_let_rec_env false env0 lbs1 in
                    (match uu____14489 with
                     | (lbs2,rec_env) ->
                         let uu____14508 = check_let_recs rec_env lbs2 in
                         (match uu____14508 with
                          | (lbs3,g_lbs) ->
                              let uu____14527 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___368_14550 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___368_14550.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___368_14550.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___369_14552 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___369_14552.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___369_14552.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___369_14552.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___369_14552.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____14527 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____14579 = tc_term env2 e21 in
                                   (match uu____14579 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____14596 =
                                            let uu____14597 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____14597 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____14596 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___370_14601 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___370_14601.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___370_14601.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___370_14601.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____14602 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____14602 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____14638 ->
                                                  (e, cres2, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  let cres3 =
                                                    let uu___371_14643 =
                                                      cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___371_14643.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___371_14643.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___371_14643.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____14646 -> failwith "Impossible"
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
          let uu____14675 = FStar_Options.ml_ish () in
          if uu____14675
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp in
             let uu____14678 =
               let uu____14683 =
                 let uu____14684 = FStar_Syntax_Subst.compress t in
                 uu____14684.FStar_Syntax_Syntax.n in
               let uu____14687 =
                 let uu____14688 = FStar_Syntax_Subst.compress lbdef in
                 uu____14688.FStar_Syntax_Syntax.n in
               (uu____14683, uu____14687) in
             match uu____14678 with
             | (FStar_Syntax_Syntax.Tm_arrow
                (formals,c),FStar_Syntax_Syntax.Tm_abs
                (actuals,uu____14694,uu____14695)) ->
                 let actuals1 =
                   let uu____14733 =
                     FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                   FStar_TypeChecker_Util.maybe_add_implicit_binders
                     uu____14733 actuals in
                 (if
                    (FStar_List.length formals) <>
                      (FStar_List.length actuals1)
                  then
                    (let actuals_msg =
                       let n1 = FStar_List.length actuals1 in
                       if n1 = (Prims.parse_int "1")
                       then "1 argument was found"
                       else
                         (let uu____14754 = FStar_Util.string_of_int n1 in
                          FStar_Util.format1 "%s arguments were found"
                            uu____14754) in
                     let formals_msg =
                       let n1 = FStar_List.length formals in
                       if n1 = (Prims.parse_int "1")
                       then "1 argument"
                       else
                         (let uu____14772 = FStar_Util.string_of_int n1 in
                          FStar_Util.format1 "%s arguments" uu____14772) in
                     let msg =
                       let uu____14780 =
                         FStar_Syntax_Print.term_to_string lbtyp in
                       let uu____14781 =
                         FStar_Syntax_Print.lbname_to_string lbname in
                       FStar_Util.format4
                         "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                         uu____14780 uu____14781 formals_msg actuals_msg in
                     FStar_Exn.raise
                       (FStar_Errors.Error
                          (msg, (lbdef.FStar_Syntax_Syntax.pos))))
                  else ();
                  (let quals =
                     FStar_TypeChecker_Env.lookup_effect_quals env
                       (FStar_Syntax_Util.comp_effect_name c) in
                   FStar_All.pipe_right quals
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
             | uu____14788 ->
                 let uu____14793 =
                   let uu____14794 =
                     let uu____14799 =
                       let uu____14800 =
                         FStar_Syntax_Print.term_to_string lbdef in
                       let uu____14801 =
                         FStar_Syntax_Print.term_to_string lbtyp in
                       FStar_Util.format2
                         "Only function literals with arrow types can be defined recursively; got %s : %s"
                         uu____14800 uu____14801 in
                     (uu____14799, (lbtyp.FStar_Syntax_Syntax.pos)) in
                   FStar_Errors.Error uu____14794 in
                 FStar_Exn.raise uu____14793) in
        let uu____14802 =
          FStar_List.fold_left
            (fun uu____14828  ->
               fun lb  ->
                 match uu____14828 with
                 | (lbs1,env1) ->
                     let uu____14848 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____14848 with
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
                              (let uu____14868 =
                                 let uu____14875 =
                                   let uu____14876 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____14876 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___372_14887 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___372_14887.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___372_14887.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___372_14887.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___372_14887.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___372_14887.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___372_14887.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___372_14887.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___372_14887.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___372_14887.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___372_14887.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___372_14887.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___372_14887.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___372_14887.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___372_14887.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___372_14887.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___372_14887.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___372_14887.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___372_14887.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___372_14887.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___372_14887.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___372_14887.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___372_14887.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___372_14887.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___372_14887.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___372_14887.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___372_14887.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___372_14887.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___372_14887.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___372_14887.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___372_14887.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___372_14887.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___372_14887.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___372_14887.FStar_TypeChecker_Env.dep_graph)
                                    }) t uu____14875 in
                               match uu____14868 with
                               | (t1,uu____14889,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____14893 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____14893);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____14895 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____14895
                            then
                              let uu___373_14896 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___373_14896.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___373_14896.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___373_14896.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___373_14896.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___373_14896.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___373_14896.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___373_14896.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___373_14896.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___373_14896.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___373_14896.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___373_14896.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___373_14896.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___373_14896.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___373_14896.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___373_14896.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___373_14896.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___373_14896.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___373_14896.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___373_14896.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___373_14896.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___373_14896.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___373_14896.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___373_14896.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___373_14896.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___373_14896.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___373_14896.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___373_14896.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___373_14896.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___373_14896.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___373_14896.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___373_14896.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___373_14896.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___373_14896.FStar_TypeChecker_Env.dep_graph)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1) in
                          let lb1 =
                            let uu___374_14913 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___374_14913.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___374_14913.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____14802 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lbs  ->
      let uu____14936 =
        let uu____14945 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____14974 =
                     let uu____14975 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____14975.FStar_Syntax_Syntax.n in
                   match uu____14974 with
                   | FStar_Syntax_Syntax.Tm_abs uu____14978 -> ()
                   | uu____14995 ->
                       let uu____14996 =
                         let uu____14997 =
                           let uu____15002 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____15002) in
                         FStar_Errors.Error uu____14997 in
                       FStar_Exn.raise uu____14996);
                  (let uu____15003 =
                     let uu____15010 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____15010
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____15003 with
                   | (e,c,g) ->
                       ((let uu____15019 =
                           let uu____15020 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____15020 in
                         if uu____15019
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
        FStar_All.pipe_right uu____14945 FStar_List.unzip in
      match uu____14936 with
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
        let uu____15069 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____15069 with
        | (env1,uu____15087) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____15095 = check_lbtyp top_level env lb in
            (match uu____15095 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Exn.raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____15139 =
                     tc_maybe_toplevel_term
                       (let uu___375_15148 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___375_15148.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___375_15148.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___375_15148.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___375_15148.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___375_15148.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___375_15148.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___375_15148.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___375_15148.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___375_15148.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___375_15148.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___375_15148.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___375_15148.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___375_15148.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___375_15148.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___375_15148.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___375_15148.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___375_15148.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___375_15148.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___375_15148.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.failhard =
                            (uu___375_15148.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___375_15148.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___375_15148.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___375_15148.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___375_15148.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___375_15148.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___375_15148.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___375_15148.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___375_15148.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___375_15148.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___375_15148.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___375_15148.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___375_15148.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___375_15148.FStar_TypeChecker_Env.dep_graph)
                        }) e11 in
                   match uu____15139 with
                   | (e12,c1,g1) ->
                       let uu____15162 =
                         let uu____15167 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____15171  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____15167 e12 c1 wf_annot in
                       (match uu____15162 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____15186 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____15186
                              then
                                let uu____15187 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____15188 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____15189 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____15187 uu____15188 uu____15189
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
        | uu____15233 ->
            let uu____15234 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____15234 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____15283 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____15283)
                 else
                   (let uu____15291 = FStar_Syntax_Util.type_u () in
                    match uu____15291 with
                    | (k,uu____15311) ->
                        let uu____15312 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____15312 with
                         | (t2,uu____15334,g) ->
                             ((let uu____15337 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____15337
                               then
                                 let uu____15338 =
                                   let uu____15339 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____15339 in
                                 let uu____15340 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____15338 uu____15340
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____15343 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____15343))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun uu____15351  ->
      match uu____15351 with
      | (x,imp) ->
          let uu____15370 = FStar_Syntax_Util.type_u () in
          (match uu____15370 with
           | (tu,u) ->
               ((let uu____15390 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____15390
                 then
                   let uu____15391 = FStar_Syntax_Print.bv_to_string x in
                   let uu____15392 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____15393 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____15391 uu____15392 uu____15393
                 else ());
                (let uu____15395 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____15395 with
                 | (t,uu____15415,g) ->
                     let x1 =
                       ((let uu___376_15423 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___376_15423.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___376_15423.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____15425 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____15425
                       then
                         let uu____15426 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1) in
                         let uu____15427 =
                           FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____15426 uu____15427
                       else ());
                      (let uu____15429 = push_binding env x1 in
                       (x1, uu____15429, g, u))))))
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
            let uu____15519 = tc_binder env1 b in
            (match uu____15519 with
             | (b1,env',g,u) ->
                 let uu____15560 = aux env' bs2 in
                 (match uu____15560 with
                  | (bs3,env'1,g',us) ->
                      let uu____15613 =
                        let uu____15614 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____15614 in
                      ((b1 :: bs3), env'1, uu____15613, (u :: us)))) in
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
          (fun uu____15699  ->
             fun uu____15700  ->
               match (uu____15699, uu____15700) with
               | ((t,imp),(args1,g)) ->
                   let uu____15769 = tc_term env1 t in
                   (match uu____15769 with
                    | (t1,uu____15787,g') ->
                        let uu____15789 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____15789))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____15831  ->
             match uu____15831 with
             | (pats1,g) ->
                 let uu____15856 = tc_args env p in
                 (match uu____15856 with
                  | (args,g') ->
                      let uu____15869 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____15869))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let uu____15882 = tc_maybe_toplevel_term env e in
      match uu____15882 with
      | (e1,c,g) ->
          let uu____15898 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____15898
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____15911 =
               let uu____15916 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____15916
               then
                 let uu____15921 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____15921, false)
               else
                 (let uu____15923 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____15923, true)) in
             match uu____15911 with
             | (target_comp,allow_ghost) ->
                 let uu____15932 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____15932 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____15942 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____15942)
                  | uu____15943 ->
                      if allow_ghost
                      then
                        let uu____15952 =
                          let uu____15953 =
                            let uu____15958 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____15958, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____15953 in
                        FStar_Exn.raise uu____15952
                      else
                        (let uu____15966 =
                           let uu____15967 =
                             let uu____15972 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____15972, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____15967 in
                         FStar_Exn.raise uu____15966)))
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
      let uu____15991 = tc_tot_or_gtot_term env t in
      match uu____15991 with
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
      (let uu____16019 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____16019
       then
         let uu____16020 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____16020
       else ());
      (let env1 =
         let uu___377_16023 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___377_16023.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___377_16023.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___377_16023.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___377_16023.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___377_16023.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___377_16023.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___377_16023.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___377_16023.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___377_16023.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___377_16023.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___377_16023.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___377_16023.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___377_16023.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___377_16023.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___377_16023.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___377_16023.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___377_16023.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___377_16023.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___377_16023.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___377_16023.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___377_16023.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___377_16023.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___377_16023.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___377_16023.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___377_16023.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___377_16023.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___377_16023.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___377_16023.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___377_16023.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___377_16023.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___377_16023.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___377_16023.FStar_TypeChecker_Env.dep_graph)
         } in
       let uu____16028 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____16061) ->
             let uu____16062 =
               let uu____16063 =
                 let uu____16068 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____16068) in
               FStar_Errors.Error uu____16063 in
             FStar_Exn.raise uu____16062 in
       match uu____16028 with
       | (t,c,g) ->
           let uu____16084 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____16084
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____16094 =
                let uu____16095 =
                  let uu____16100 =
                    let uu____16101 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____16101 in
                  let uu____16102 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____16100, uu____16102) in
                FStar_Errors.Error uu____16095 in
              FStar_Exn.raise uu____16094))
let level_of_type_fail:
  'Auu____16113 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____16113
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____16126 =
          let uu____16127 =
            let uu____16132 =
              let uu____16133 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format2
                "Expected a term of type 'Type'; got %s : %s" uu____16133 t in
            let uu____16134 = FStar_TypeChecker_Env.get_range env in
            (uu____16132, uu____16134) in
          FStar_Errors.Error uu____16127 in
        FStar_Exn.raise uu____16126
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____16151 =
            let uu____16152 = FStar_Syntax_Util.unrefine t1 in
            uu____16152.FStar_Syntax_Syntax.n in
          match uu____16151 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____16156 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____16159 = FStar_Syntax_Util.type_u () in
                 match uu____16159 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___380_16167 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___380_16167.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___380_16167.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___380_16167.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___380_16167.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___380_16167.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___380_16167.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___380_16167.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___380_16167.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___380_16167.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___380_16167.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___380_16167.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___380_16167.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___380_16167.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___380_16167.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___380_16167.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___380_16167.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___380_16167.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___380_16167.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___380_16167.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___380_16167.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___380_16167.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___380_16167.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___380_16167.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___380_16167.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___380_16167.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___380_16167.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___380_16167.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___380_16167.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___380_16167.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___380_16167.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___380_16167.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___380_16167.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___380_16167.FStar_TypeChecker_Env.dep_graph)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____16171 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____16171
                       | uu____16172 ->
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
      let uu____16181 =
        let uu____16182 = FStar_Syntax_Subst.compress e in
        uu____16182.FStar_Syntax_Syntax.n in
      match uu____16181 with
      | FStar_Syntax_Syntax.Tm_bvar uu____16187 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____16192 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____16219 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____16235) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____16258,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____16285) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____16292 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____16292 with | ((uu____16303,t),uu____16305) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16310,(FStar_Util.Inl t,uu____16312),uu____16313) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16360,(FStar_Util.Inr c,uu____16362),uu____16363) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____16413;
             FStar_Syntax_Syntax.vars = uu____16414;_},us)
          ->
          let uu____16420 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____16420 with
           | ((us',t),uu____16433) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____16439 =
                     let uu____16440 =
                       let uu____16445 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____16445) in
                     FStar_Errors.Error uu____16440 in
                   FStar_Exn.raise uu____16439)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____16461 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____16462 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____16472) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____16495 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____16495 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____16515  ->
                      match uu____16515 with
                      | (b,uu____16521) ->
                          let uu____16522 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____16522) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____16527 = universe_of_aux env res in
                 level_of_type env res uu____16527 in
               let u_c =
                 let uu____16529 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____16529 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____16533 = universe_of_aux env trepr in
                     level_of_type env trepr uu____16533 in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____16626 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____16641 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____16680 ->
                let uu____16681 = universe_of_aux env hd3 in
                (uu____16681, args1)
            | FStar_Syntax_Syntax.Tm_name uu____16694 ->
                let uu____16695 = universe_of_aux env hd3 in
                (uu____16695, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____16708 ->
                let uu____16725 = universe_of_aux env hd3 in
                (uu____16725, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____16738 ->
                let uu____16745 = universe_of_aux env hd3 in
                (uu____16745, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____16758 ->
                let uu____16785 = universe_of_aux env hd3 in
                (uu____16785, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____16798 ->
                let uu____16805 = universe_of_aux env hd3 in
                (uu____16805, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____16818 ->
                let uu____16819 = universe_of_aux env hd3 in
                (uu____16819, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____16832 ->
                let uu____16845 = universe_of_aux env hd3 in
                (uu____16845, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____16858 ->
                let uu____16865 = universe_of_aux env hd3 in
                (uu____16865, args1)
            | FStar_Syntax_Syntax.Tm_type uu____16878 ->
                let uu____16879 = universe_of_aux env hd3 in
                (uu____16879, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____16892,hd4::uu____16894) ->
                let uu____16959 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____16959 with
                 | (uu____16974,uu____16975,hd5) ->
                     let uu____16993 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____16993 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____17044 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____17046 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____17046 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____17097 ->
                let uu____17098 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____17098 with
                 | (env1,uu____17120) ->
                     let env2 =
                       let uu___381_17126 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___381_17126.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___381_17126.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___381_17126.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___381_17126.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___381_17126.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___381_17126.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___381_17126.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___381_17126.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___381_17126.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___381_17126.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___381_17126.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___381_17126.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___381_17126.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___381_17126.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___381_17126.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___381_17126.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___381_17126.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___381_17126.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___381_17126.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___381_17126.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___381_17126.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___381_17126.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___381_17126.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___381_17126.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___381_17126.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___381_17126.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___381_17126.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___381_17126.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___381_17126.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___381_17126.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___381_17126.FStar_TypeChecker_Env.dep_graph)
                       } in
                     ((let uu____17128 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____17128
                       then
                         let uu____17129 =
                           let uu____17130 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____17130 in
                         let uu____17131 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____17129 uu____17131
                       else ());
                      (let uu____17133 = tc_term env2 hd3 in
                       match uu____17133 with
                       | (uu____17154,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____17155;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____17157;
                                        FStar_Syntax_Syntax.comp =
                                          uu____17158;_},g)
                           ->
                           ((let uu____17169 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____17169
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____17180 = type_of_head true hd1 args in
          (match uu____17180 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____17220 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____17220 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____17264 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____17264)))
      | FStar_Syntax_Syntax.Tm_match (uu____17267,hd1::uu____17269) ->
          let uu____17334 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____17334 with
           | (uu____17337,uu____17338,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____17356,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____17399 = universe_of_aux env e in
      level_of_type env e uu____17399
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