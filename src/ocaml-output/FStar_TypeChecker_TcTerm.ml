open Prims
let instantiate_both: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___278_4 = env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___278_4.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___278_4.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___278_4.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___278_4.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___278_4.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___278_4.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___278_4.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___278_4.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___278_4.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___278_4.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___278_4.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___278_4.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___278_4.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___278_4.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___278_4.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___278_4.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___278_4.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___278_4.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___278_4.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___278_4.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___278_4.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___278_4.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___278_4.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___278_4.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___278_4.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___278_4.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___278_4.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___278_4.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___278_4.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___278_4.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___278_4.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___278_4.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___278_4.FStar_TypeChecker_Env.dep_graph)
    }
let no_inst: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___279_8 = env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___279_8.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___279_8.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___279_8.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___279_8.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___279_8.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___279_8.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___279_8.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___279_8.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___279_8.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___279_8.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___279_8.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___279_8.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___279_8.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___279_8.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___279_8.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___279_8.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___279_8.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___279_8.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___279_8.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___279_8.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___279_8.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.tc_term =
        (uu___279_8.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___279_8.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___279_8.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___279_8.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___279_8.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___279_8.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___279_8.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___279_8.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___279_8.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___279_8.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___279_8.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.dep_graph =
        (uu___279_8.FStar_TypeChecker_Env.dep_graph)
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
  fun uu___273_53  ->
    match uu___273_53 with
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
      let uu___280_204 = lc in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___280_204.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags =
          (uu___280_204.FStar_Syntax_Syntax.cflags);
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
          let e0 = e in
          let should_return t =
            let uu____254 =
              let uu____255 = FStar_Syntax_Subst.compress t in
              uu____255.FStar_Syntax_Syntax.n in
            match uu____254 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____258,c) ->
                let uu____276 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c) in
                if uu____276
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c) in
                  let uu____278 =
                    let uu____279 = FStar_Syntax_Subst.compress t1 in
                    uu____279.FStar_Syntax_Syntax.n in
                  (match uu____278 with
                   | FStar_Syntax_Syntax.Tm_constant uu____282 -> false
                   | uu____283 ->
                       let uu____284 = FStar_Syntax_Util.is_unit t1 in
                       Prims.op_Negation uu____284)
                else false
            | uu____286 ->
                let uu____287 = FStar_Syntax_Util.is_unit t in
                Prims.op_Negation uu____287 in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____290 =
                  let uu____293 =
                    (let uu____296 = should_return t in
                     Prims.op_Negation uu____296) ||
                      (let uu____298 =
                         FStar_TypeChecker_Env.should_verify env in
                       Prims.op_Negation uu____298) in
                  if uu____293
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e in
                FStar_Syntax_Util.lcomp_of_comp uu____290
            | FStar_Util.Inr lc -> lc in
          let t = lc.FStar_Syntax_Syntax.res_typ in
          let uu____306 =
            let uu____313 = FStar_TypeChecker_Env.expected_typ env in
            match uu____313 with
            | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                ((let uu____324 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High in
                  if uu____324
                  then
                    let uu____325 = FStar_Syntax_Print.term_to_string t in
                    let uu____326 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____325
                      uu____326
                  else ());
                 (let uu____328 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t' in
                  match uu____328 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____344 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____344 with
                       | (e2,g) ->
                           ((let uu____358 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____358
                             then
                               let uu____359 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____360 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____361 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____362 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____359 uu____360 uu____361 uu____362
                             else ());
                            (let msg =
                               let uu____369 =
                                 FStar_TypeChecker_Rel.is_trivial g in
                               if uu____369
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_40  ->
                                      FStar_Pervasives_Native.Some _0_40)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             let uu____386 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1 in
                             match uu____386 with
                             | (lc2,g2) ->
                                 ((memo_tk e2 t'), (set_lcomp_result lc2 t'),
                                   g2)))))) in
          match uu____306 with
          | (e1,lc1,g) ->
              ((let uu____409 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low in
                if uu____409
                then
                  let uu____410 = FStar_Syntax_Print.lcomp_to_string lc1 in
                  FStar_Util.print1 "Return comp type is %s\n" uu____410
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
        let uu____433 = FStar_TypeChecker_Env.expected_typ env in
        match uu____433 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____443 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____443 with
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
      fun uu____476  ->
        match uu____476 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____505 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____505
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____507 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____507
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____509 =
              match copt with
              | FStar_Pervasives_Native.Some uu____522 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____525 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____527 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____527)) in
                  if uu____525
                  then
                    let uu____534 =
                      let uu____537 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos in
                      FStar_Pervasives_Native.Some uu____537 in
                    (uu____534, c)
                  else
                    (let uu____541 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____541
                     then
                       let uu____548 = tot_or_gtot c in
                       (FStar_Pervasives_Native.None, uu____548)
                     else
                       (let uu____552 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____552
                        then
                          let uu____559 =
                            let uu____562 = tot_or_gtot c in
                            FStar_Pervasives_Native.Some uu____562 in
                          (uu____559, c)
                        else (FStar_Pervasives_Native.None, c))) in
            (match uu____509 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let uu____588 =
                        FStar_TypeChecker_Util.check_comp env e c2 expected_c in
                      (match uu____588 with
                       | (e1,uu____602,g) ->
                           let g1 =
                             let uu____605 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_TypeChecker_Util.label_guard uu____605
                               "could not prove post-condition" g in
                           ((let uu____607 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low in
                             if uu____607
                             then
                               let uu____608 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos in
                               let uu____609 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1 in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____608 uu____609
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c2)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c2) in
                             (e2, expected_c, g1))))))
let no_logical_guard:
  'Auu____616 'Auu____617 .
    FStar_TypeChecker_Env.env ->
      ('Auu____617,'Auu____616,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____617,'Auu____616,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____637  ->
      match uu____637 with
      | (te,kt,f) ->
          let uu____647 = FStar_TypeChecker_Rel.guard_form f in
          (match uu____647 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____655 =
                 let uu____656 =
                   let uu____661 =
                     FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                       env f1 in
                   let uu____662 = FStar_TypeChecker_Env.get_range env in
                   (uu____661, uu____662) in
                 FStar_Errors.Error uu____656 in
               FStar_Exn.raise uu____655)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____672 = FStar_TypeChecker_Env.expected_typ env in
    match uu____672 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____676 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____676
let rec get_pat_vars:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun pats  ->
    fun acc  ->
      let pats1 = FStar_Syntax_Util.unmeta pats in
      let uu____700 = FStar_Syntax_Util.head_and_args pats1 in
      match uu____700 with
      | (head1,args) ->
          let uu____739 =
            let uu____740 = FStar_Syntax_Util.un_uinst head1 in
            uu____740.FStar_Syntax_Syntax.n in
          (match uu____739 with
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid
               ->
               let uu____747 = FStar_List.tl args in
               get_pat_vars_args uu____747 acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.smtpatOr_lid
               -> get_pat_vars_args args acc
           | FStar_Syntax_Syntax.Tm_fvar fv when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               -> get_pat_vars_args args acc
           | uu____756 ->
               let uu____757 = FStar_Syntax_Free.names pats1 in
               FStar_Util.set_union acc uu____757)
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
  'Auu____787 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,'Auu____787) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____820 = FStar_Syntax_Util.is_smt_lemma t in
          if uu____820
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____821;
                  FStar_Syntax_Syntax.effect_name = uu____822;
                  FStar_Syntax_Syntax.result_typ = uu____823;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____827)::[];
                  FStar_Syntax_Syntax.flags = uu____828;_}
                ->
                let pat_vars =
                  let uu____876 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta] env pats in
                  let uu____877 =
                    FStar_Util.new_set FStar_Syntax_Syntax.order_bv in
                  get_pat_vars uu____876 uu____877 in
                let uu____880 =
                  FStar_All.pipe_right bs
                    (FStar_Util.find_opt
                       (fun uu____907  ->
                          match uu____907 with
                          | (b,uu____913) ->
                              let uu____914 = FStar_Util.set_mem b pat_vars in
                              Prims.op_Negation uu____914)) in
                (match uu____880 with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some (x,uu____920) ->
                     let uu____925 =
                       let uu____926 = FStar_Syntax_Print.bv_to_string x in
                       FStar_Util.format1
                         "Pattern misses at least one bound variable: %s"
                         uu____926 in
                     FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____925)
            | uu____927 -> failwith "Impossible"
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
        match env.FStar_TypeChecker_Env.letrecs with
        | [] -> []
        | letrecs ->
            let r = FStar_TypeChecker_Env.get_range env in
            let env1 =
              let uu___281_981 = env in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___281_981.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___281_981.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___281_981.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___281_981.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___281_981.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___281_981.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___281_981.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___281_981.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___281_981.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___281_981.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___281_981.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___281_981.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___281_981.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___281_981.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___281_981.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___281_981.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___281_981.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___281_981.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___281_981.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.failhard =
                  (uu___281_981.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___281_981.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.tc_term =
                  (uu___281_981.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___281_981.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___281_981.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___281_981.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qname_and_index =
                  (uu___281_981.FStar_TypeChecker_Env.qname_and_index);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___281_981.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth =
                  (uu___281_981.FStar_TypeChecker_Env.synth);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___281_981.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___281_981.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___281_981.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___281_981.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.dep_graph =
                  (uu___281_981.FStar_TypeChecker_Env.dep_graph)
              } in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid in
            let decreases_clause bs c =
              let filter_types_and_functions bs1 =
                FStar_All.pipe_right bs1
                  (FStar_List.collect
                     (fun uu____1017  ->
                        match uu____1017 with
                        | (b,uu____1025) ->
                            let t =
                              let uu____1027 =
                                FStar_Syntax_Util.unrefine
                                  b.FStar_Syntax_Syntax.sort in
                              FStar_TypeChecker_Normalize.unfold_whnf env1
                                uu____1027 in
                            (match t.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_type uu____1030 -> []
                             | FStar_Syntax_Syntax.Tm_arrow uu____1031 -> []
                             | uu____1044 ->
                                 let uu____1045 =
                                   FStar_Syntax_Syntax.bv_to_name b in
                                 [uu____1045]))) in
              let as_lex_list dec =
                let uu____1050 = FStar_Syntax_Util.head_and_args dec in
                match uu____1050 with
                | (head1,uu____1066) ->
                    (match head1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.lexcons_lid
                         -> dec
                     | uu____1088 -> mk_lex_list [dec]) in
              let cflags = FStar_Syntax_Util.comp_flags c in
              let uu____1092 =
                FStar_All.pipe_right cflags
                  (FStar_List.tryFind
                     (fun uu___274_1101  ->
                        match uu___274_1101 with
                        | FStar_Syntax_Syntax.DECREASES uu____1102 -> true
                        | uu____1105 -> false)) in
              match uu____1092 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                  dec) -> as_lex_list dec
              | uu____1109 ->
                  let xs = FStar_All.pipe_right bs filter_types_and_functions in
                  (match xs with | x::[] -> x | uu____1118 -> mk_lex_list xs) in
            let previous_dec = decreases_clause actuals expected_c in
            let guard_one_letrec uu____1139 =
              match uu____1139 with
              | (l,t,u_names) ->
                  let uu____1157 =
                    let uu____1158 = FStar_Syntax_Subst.compress t in
                    uu____1158.FStar_Syntax_Syntax.n in
                  (match uu____1157 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____1219  ->
                                 match uu____1219 with
                                 | (x,imp) ->
                                     let uu____1230 =
                                       FStar_Syntax_Syntax.is_null_bv x in
                                     if uu____1230
                                     then
                                       let uu____1235 =
                                         let uu____1236 =
                                           let uu____1239 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x in
                                           FStar_Pervasives_Native.Some
                                             uu____1239 in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____1236
                                           x.FStar_Syntax_Syntax.sort in
                                       (uu____1235, imp)
                                     else (x, imp))) in
                       let uu____1241 =
                         FStar_Syntax_Subst.open_comp formals1 c in
                       (match uu____1241 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1 in
                            let precedes1 =
                              let uu____1260 =
                                let uu____1261 =
                                  let uu____1262 =
                                    FStar_Syntax_Syntax.as_arg dec in
                                  let uu____1263 =
                                    let uu____1266 =
                                      FStar_Syntax_Syntax.as_arg previous_dec in
                                    [uu____1266] in
                                  uu____1262 :: uu____1263 in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____1261 in
                              uu____1260 FStar_Pervasives_Native.None r in
                            let uu____1269 = FStar_Util.prefix formals2 in
                            (match uu____1269 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___282_1316 = last1 in
                                   let uu____1317 =
                                     FStar_Syntax_Util.refine last1 precedes1 in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___282_1316.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___282_1316.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____1317
                                   } in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)] in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1 in
                                 ((let uu____1343 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low in
                                   if uu____1343
                                   then
                                     let uu____1344 =
                                       FStar_Syntax_Print.lbname_to_string l in
                                     let uu____1345 =
                                       FStar_Syntax_Print.term_to_string t in
                                     let uu____1346 =
                                       FStar_Syntax_Print.term_to_string t' in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____1344 uu____1345 uu____1346
                                   else ());
                                  (l, t', u_names))))
                   | uu____1350 ->
                       FStar_Exn.raise
                         (FStar_Errors.Error
                            ("Annotated type of 'let rec' must be an arrow",
                              (t.FStar_Syntax_Syntax.pos)))) in
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
        (let uu___283_1793 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___283_1793.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___283_1793.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___283_1793.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___283_1793.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___283_1793.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___283_1793.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___283_1793.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___283_1793.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___283_1793.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___283_1793.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___283_1793.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___283_1793.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___283_1793.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___283_1793.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___283_1793.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___283_1793.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___283_1793.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___283_1793.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___283_1793.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___283_1793.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___283_1793.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___283_1793.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___283_1793.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___283_1793.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___283_1793.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___283_1793.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___283_1793.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___283_1793.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___283_1793.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___283_1793.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___283_1793.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___283_1793.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___283_1793.FStar_TypeChecker_Env.dep_graph)
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
      (let uu____1805 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1805
       then
         let uu____1806 =
           let uu____1807 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1807 in
         let uu____1808 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1806 uu____1808
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1817 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1848 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1855 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1872 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1873 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1874 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1875 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1876 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1893 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1906 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1913 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____1914;
              FStar_Syntax_Syntax.vars = uu____1915;_},FStar_Syntax_Syntax.Meta_alien
            (uu____1916,uu____1917,ty))
           ->
           let uu____1927 =
             let uu____1928 = FStar_Syntax_Syntax.mk_Total ty in
             FStar_All.pipe_right uu____1928 FStar_Syntax_Util.lcomp_of_comp in
           (top, uu____1927, FStar_TypeChecker_Rel.trivial_guard)
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1934 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1934 with
            | (e2,c,g) ->
                let g1 =
                  let uu___284_1951 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___284_1951.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___284_1951.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___284_1951.FStar_TypeChecker_Env.implicits)
                  } in
                let uu____1952 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (uu____1952, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1973 = FStar_Syntax_Util.type_u () in
           (match uu____1973 with
            | (t,u) ->
                let uu____1986 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1986 with
                 | (e2,c,g) ->
                     let uu____2002 =
                       let uu____2017 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____2017 with
                       | (env2,uu____2039) -> tc_pats env2 pats in
                     (match uu____2002 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___285_2073 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___285_2073.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___285_2073.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___285_2073.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____2074 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____2077 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____2074, c, uu____2077))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____2085 =
             let uu____2086 = FStar_Syntax_Subst.compress e1 in
             uu____2086.FStar_Syntax_Syntax.n in
           (match uu____2085 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____2095,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____2097;
                               FStar_Syntax_Syntax.lbtyp = uu____2098;
                               FStar_Syntax_Syntax.lbeff = uu____2099;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____2124 =
                  let uu____2131 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit in
                  tc_term uu____2131 e11 in
                (match uu____2124 with
                 | (e12,c1,g1) ->
                     let uu____2141 = tc_term env1 e2 in
                     (match uu____2141 with
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
                            let uu____2165 =
                              let uu____2168 =
                                let uu____2169 =
                                  let uu____2182 =
                                    let uu____2189 =
                                      let uu____2192 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13) in
                                      [uu____2192] in
                                    (false, uu____2189) in
                                  (uu____2182, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____2169 in
                              FStar_Syntax_Syntax.mk uu____2168 in
                            uu____2165 FStar_Pervasives_Native.None
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
                          let uu____2214 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____2214)))
            | uu____2217 ->
                let uu____2218 = tc_term env1 e1 in
                (match uu____2218 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2240) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____2252) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____2271 = tc_term env1 e1 in
           (match uu____2271 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____2295) ->
           let uu____2342 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2342 with
            | (env0,uu____2356) ->
                let uu____2361 = tc_comp env0 expected_c in
                (match uu____2361 with
                 | (expected_c1,uu____2375,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____2380 =
                       let uu____2387 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____2387 e1 in
                     (match uu____2380 with
                      | (e2,c',g') ->
                          let uu____2397 =
                            let uu____2404 =
                              let uu____2409 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____2409) in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____2404 in
                          (match uu____2397 with
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
                                 let uu____2458 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____2458 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____2467 =
                                            FStar_Syntax_Util.mk_squash f1 in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____2467) in
                               let uu____2468 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____2468 with
                                | (e5,c,f2) ->
                                    let final_guard =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, final_guard))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____2488) ->
           let uu____2535 = FStar_Syntax_Util.type_u () in
           (match uu____2535 with
            | (k,u) ->
                let uu____2548 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____2548 with
                 | (t1,uu____2562,f) ->
                     let uu____2564 =
                       let uu____2571 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____2571 e1 in
                     (match uu____2564 with
                      | (e2,c,g) ->
                          let uu____2581 =
                            let uu____2586 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____2590  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____2586 e2 c f in
                          (match uu____2581 with
                           | (c1,f1) ->
                               let uu____2599 =
                                 let uu____2606 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2,
                                          ((FStar_Util.Inl t1),
                                            FStar_Pervasives_Native.None),
                                          (FStar_Pervasives_Native.Some
                                             (c1.FStar_Syntax_Syntax.eff_name))))
                                     FStar_Pervasives_Native.None
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____2606 c1 in
                               (match uu____2599 with
                                | (e3,c2,f2) ->
                                    let uu____2646 =
                                      let uu____2647 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____2647 in
                                    (e3, c2, uu____2646))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____2648;
              FStar_Syntax_Syntax.vars = uu____2649;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2712 = FStar_Syntax_Util.head_and_args top in
           (match uu____2712 with
            | (unary_op,uu____2734) ->
                let head1 =
                  let uu____2758 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2758 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____2796;
              FStar_Syntax_Syntax.vars = uu____2797;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2860 = FStar_Syntax_Util.head_and_args top in
           (match uu____2860 with
            | (unary_op,uu____2882) ->
                let head1 =
                  let uu____2906 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2906 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____2944);
              FStar_Syntax_Syntax.pos = uu____2945;
              FStar_Syntax_Syntax.vars = uu____2946;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____3009 = FStar_Syntax_Util.head_and_args top in
           (match uu____3009 with
            | (unary_op,uu____3031) ->
                let head1 =
                  let uu____3055 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____3055 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3093;
              FStar_Syntax_Syntax.vars = uu____3094;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____3170 = FStar_Syntax_Util.head_and_args top in
           (match uu____3170 with
            | (unary_op,uu____3192) ->
                let head1 =
                  let uu____3216 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))
                    FStar_Pervasives_Native.None uu____3216 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3260;
              FStar_Syntax_Syntax.vars = uu____3261;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____3299 =
             let uu____3306 =
               let uu____3307 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3307 in
             tc_term uu____3306 e1 in
           (match uu____3299 with
            | (e2,c,g) ->
                let uu____3331 = FStar_Syntax_Util.head_and_args top in
                (match uu____3331 with
                 | (head1,uu____3353) ->
                     let uu____3374 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos in
                     let uu____3401 =
                       let uu____3402 =
                         let uu____3405 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid in
                         FStar_Syntax_Syntax.mk_Total uu____3405 in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____3402 in
                     (uu____3374, uu____3401, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3410;
              FStar_Syntax_Syntax.vars = uu____3411;_},(a1,FStar_Pervasives_Native.None
                                                        )::(a2,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____3464 = FStar_Syntax_Util.head_and_args top in
           (match uu____3464 with
            | (head1,uu____3486) ->
                let env' =
                  let uu____3508 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____3508 in
                let uu____3509 = tc_term env' a1 in
                (match uu____3509 with
                 | (e1,uu____3523,g1) ->
                     let uu____3525 = tc_term env1 a2 in
                     (match uu____3525 with
                      | (e2,t2,g2) ->
                          let g = FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          let uu____3542 =
                            let uu____3545 =
                              let uu____3546 =
                                let uu____3547 =
                                  FStar_Syntax_Syntax.as_arg a1 in
                                let uu____3548 =
                                  let uu____3551 =
                                    FStar_Syntax_Syntax.as_arg a2 in
                                  [uu____3551] in
                                uu____3547 :: uu____3548 in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____3546 in
                            uu____3545 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          (uu____3542, t2, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____3556;
              FStar_Syntax_Syntax.vars = uu____3557;_},uu____3558)
           ->
           let uu____3579 =
             let uu____3580 =
               let uu____3585 =
                 let uu____3586 = FStar_Syntax_Print.term_to_string top in
                 FStar_Util.format1 "Ill-applied constant %s" uu____3586 in
               (uu____3585, (e.FStar_Syntax_Syntax.pos)) in
             FStar_Errors.Error uu____3580 in
           FStar_Exn.raise uu____3579
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____3593;
              FStar_Syntax_Syntax.vars = uu____3594;_},uu____3595)
           ->
           let uu____3616 =
             let uu____3617 =
               let uu____3622 =
                 let uu____3623 = FStar_Syntax_Print.term_to_string top in
                 FStar_Util.format1 "Ill-applied constant %s" uu____3623 in
               (uu____3622, (e.FStar_Syntax_Syntax.pos)) in
             FStar_Errors.Error uu____3617 in
           FStar_Exn.raise uu____3616
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____3630;
              FStar_Syntax_Syntax.vars = uu____3631;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____3664 = FStar_TypeChecker_Env.clear_expected_typ env1 in
             match uu____3664 with
             | (env0,uu____3678) ->
                 let uu____3683 = tc_term env0 e1 in
                 (match uu____3683 with
                  | (e2,c,g) ->
                      let uu____3699 = FStar_Syntax_Util.head_and_args top in
                      (match uu____3699 with
                       | (reify_op,uu____3721) ->
                           let u_c =
                             let uu____3743 =
                               tc_term env0 c.FStar_Syntax_Syntax.res_typ in
                             match uu____3743 with
                             | (uu____3750,c',uu____3752) ->
                                 let uu____3753 =
                                   let uu____3754 =
                                     FStar_Syntax_Subst.compress
                                       c'.FStar_Syntax_Syntax.res_typ in
                                   uu____3754.FStar_Syntax_Syntax.n in
                                 (match uu____3753 with
                                  | FStar_Syntax_Syntax.Tm_type u -> u
                                  | uu____3758 ->
                                      let uu____3759 =
                                        FStar_Syntax_Util.type_u () in
                                      (match uu____3759 with
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
                                                 let uu____3771 =
                                                   let uu____3772 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       c' in
                                                   let uu____3773 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c.FStar_Syntax_Syntax.res_typ in
                                                   let uu____3774 =
                                                     FStar_Syntax_Print.term_to_string
                                                       c'.FStar_Syntax_Syntax.res_typ in
                                                   FStar_Util.format3
                                                     "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                     uu____3772 uu____3773
                                                     uu____3774 in
                                                 failwith uu____3771);
                                            u))) in
                           let repr =
                             let uu____3776 = c.FStar_Syntax_Syntax.comp () in
                             FStar_TypeChecker_Env.reify_comp env1 uu____3776
                               u_c in
                           let e3 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app
                                  (reify_op, [(e2, aqual)]))
                               FStar_Pervasives_Native.None
                               top.FStar_Syntax_Syntax.pos in
                           let c1 =
                             let uu____3797 =
                               FStar_Syntax_Syntax.mk_Total repr in
                             FStar_All.pipe_right uu____3797
                               FStar_Syntax_Util.lcomp_of_comp in
                           let uu____3798 =
                             comp_check_expected_typ env1 e3 c1 in
                           (match uu____3798 with
                            | (e4,c2,g') ->
                                let uu____3814 =
                                  FStar_TypeChecker_Rel.conj_guard g g' in
                                (e4, c2, uu____3814))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____3816;
              FStar_Syntax_Syntax.vars = uu____3817;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____3859 =
               let uu____3860 =
                 let uu____3861 =
                   let uu____3866 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____3866, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____3861 in
               FStar_Exn.raise uu____3860 in
             let uu____3873 = FStar_Syntax_Util.head_and_args top in
             match uu____3873 with
             | (reflect_op,uu____3895) ->
                 let uu____3916 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____3916 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____3949 =
                        let uu____3950 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____3950 in
                      if uu____3949
                      then no_reflect ()
                      else
                        (let uu____3960 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____3960 with
                         | (env_no_ex,topt) ->
                             let uu____3979 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____3999 =
                                   let uu____4002 =
                                     let uu____4003 =
                                       let uu____4018 =
                                         let uu____4021 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____4022 =
                                           let uu____4025 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____4025] in
                                         uu____4021 :: uu____4022 in
                                       (repr, uu____4018) in
                                     FStar_Syntax_Syntax.Tm_app uu____4003 in
                                   FStar_Syntax_Syntax.mk uu____4002 in
                                 uu____3999 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos in
                               let uu____4031 =
                                 let uu____4038 =
                                   let uu____4039 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____4039
                                     FStar_Pervasives_Native.fst in
                                 tc_tot_or_gtot_term uu____4038 t in
                               match uu____4031 with
                               | (t1,uu____4067,g) ->
                                   let uu____4069 =
                                     let uu____4070 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____4070.FStar_Syntax_Syntax.n in
                                   (match uu____4069 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____4085,(res,uu____4087)::
                                         (wp,uu____4089)::[])
                                        -> (t1, res, wp, g)
                                    | uu____4132 -> failwith "Impossible") in
                             (match uu____3979 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____4163 =
                                    let uu____4168 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____4168 with
                                    | (e2,c,g) ->
                                        ((let uu____4183 =
                                            let uu____4184 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____4184 in
                                          if uu____4183
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____4194 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____4194 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____4202 =
                                                  let uu____4209 =
                                                    let uu____4214 =
                                                      let uu____4215 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____4216 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____4215 uu____4216 in
                                                    (uu____4214,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____4209] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____4202);
                                               (let uu____4225 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____4225)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____4227 =
                                                let uu____4228 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____4228 in
                                              (e2, uu____4227))) in
                                  (match uu____4163 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____4238 =
                                           let uu____4239 =
                                             let uu____4240 =
                                               let uu____4241 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____4241] in
                                             let uu____4242 =
                                               let uu____4251 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____4251] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____4240;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____4242;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____4239 in
                                         FStar_All.pipe_right uu____4238
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____4271 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____4271 with
                                        | (e4,c1,g') ->
                                            let uu____4287 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____4287))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____4334 =
               let uu____4335 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____4335 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____4334 instantiate_both in
           ((let uu____4351 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____4351
             then
               let uu____4352 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____4353 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____4352
                 uu____4353
             else ());
            (let isquote =
               let uu____4356 = FStar_Syntax_Util.head_and_args head1 in
               match uu____4356 with
               | (head2,uu____4372) ->
                   let uu____4393 =
                     let uu____4394 = FStar_Syntax_Util.un_uinst head2 in
                     uu____4394.FStar_Syntax_Syntax.n in
                   (match uu____4393 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.quote_lid
                        -> true
                    | uu____4398 -> false) in
             let uu____4399 = tc_term (no_inst env2) head1 in
             match uu____4399 with
             | (head2,chead,g_head) ->
                 let uu____4415 =
                   let uu____4422 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____4422
                   then
                     let uu____4429 =
                       let uu____4436 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____4436 in
                     match uu____4429 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____4449 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____4451 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c in
                                 Prims.op_Negation uu____4451))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                           if uu____4449
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c in
                         (e1, c1, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2 in
                      let uu____4456 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env3 head2 chead g_head args
                        uu____4456) in
                 (match uu____4415 with
                  | (e1,c,g) ->
                      ((let uu____4469 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____4469
                        then
                          let uu____4470 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____4470
                        else ());
                       (let uu____4472 = comp_check_expected_typ env0 e1 c in
                        match uu____4472 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____4489 =
                                let uu____4490 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____4490.FStar_Syntax_Syntax.n in
                              match uu____4489 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____4494) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___286_4556 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___286_4556.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___286_4556.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___286_4556.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____4605 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____4607 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____4607 in
                            ((let uu____4609 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____4609
                              then
                                let uu____4610 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____4611 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____4610 uu____4611
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____4651 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____4651 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____4671 = tc_term env12 e1 in
                (match uu____4671 with
                 | (e11,c1,g1) ->
                     let uu____4687 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____4697 = FStar_Syntax_Util.type_u () in
                           (match uu____4697 with
                            | (k,uu____4707) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____4709 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____4709, res_t)) in
                     (match uu____4687 with
                      | (env_branches,res_t) ->
                          ((let uu____4719 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____4719
                            then
                              let uu____4720 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____4720
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____4806 =
                              let uu____4811 =
                                FStar_List.fold_right
                                  (fun uu____4857  ->
                                     fun uu____4858  ->
                                       match (uu____4857, uu____4858) with
                                       | ((uu____4921,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____4981 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____4981))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____4811 with
                              | (cases,g) ->
                                  let uu____5020 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____5020, g) in
                            match uu____4806 with
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
                                           (fun uu____5116  ->
                                              match uu____5116 with
                                              | ((pat,wopt,br),uu____5144,lc,uu____5146)
                                                  ->
                                                  let uu____5159 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____5159))) in
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
                                  let uu____5214 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____5214
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____5221 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____5221 in
                                     let lb =
                                       let uu____5225 =
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
                                           uu____5225;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____5229 =
                                         let uu____5232 =
                                           let uu____5233 =
                                             let uu____5246 =
                                               let uu____5247 =
                                                 let uu____5248 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____5248] in
                                               FStar_Syntax_Subst.close
                                                 uu____5247 e_match in
                                             ((false, [lb]), uu____5246) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____5233 in
                                         FStar_Syntax_Syntax.mk uu____5232 in
                                       uu____5229
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____5261 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____5261
                                  then
                                    let uu____5262 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____5263 =
                                      let uu____5264 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____5264 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____5262 uu____5263
                                  else ());
                                 (let uu____5266 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____5266))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5269;
                FStar_Syntax_Syntax.lbunivs = uu____5270;
                FStar_Syntax_Syntax.lbtyp = uu____5271;
                FStar_Syntax_Syntax.lbeff = uu____5272;
                FStar_Syntax_Syntax.lbdef = uu____5273;_}::[]),uu____5274)
           ->
           ((let uu____5294 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5294
             then
               let uu____5295 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____5295
             else ());
            (let uu____5297 = FStar_Options.use_two_phase_tc () in
             if uu____5297
             then
               let is_lb_unannotated t =
                 match t.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_let
                     ((uu____5308,lb::[]),uu____5310) ->
                     let uu____5323 =
                       let uu____5324 =
                         FStar_Syntax_Subst.compress
                           lb.FStar_Syntax_Syntax.lbtyp in
                       uu____5324.FStar_Syntax_Syntax.n in
                     uu____5323 = FStar_Syntax_Syntax.Tm_unknown
                 | uu____5327 -> failwith "Impossible" in
               let drop_lbtyp t =
                 match t.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_let ((t1,lb::[]),t2) ->
                     let uu___287_5347 = t in
                     let uu____5348 =
                       let uu____5349 =
                         let uu____5362 =
                           let uu____5369 =
                             let uu____5372 =
                               let uu___288_5373 = lb in
                               let uu____5374 =
                                 FStar_Syntax_Syntax.mk
                                   FStar_Syntax_Syntax.Tm_unknown
                                   FStar_Pervasives_Native.None
                                   (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.pos in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___288_5373.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___288_5373.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = uu____5374;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___288_5373.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___288_5373.FStar_Syntax_Syntax.lbdef)
                               } in
                             [uu____5372] in
                           (t1, uu____5369) in
                         (uu____5362, t2) in
                       FStar_Syntax_Syntax.Tm_let uu____5349 in
                     {
                       FStar_Syntax_Syntax.n = uu____5348;
                       FStar_Syntax_Syntax.pos =
                         (uu___287_5347.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___287_5347.FStar_Syntax_Syntax.vars)
                     }
                 | uu____5387 -> failwith "Impossible" in
               let uu____5388 =
                 check_top_level_let
                   (let uu___289_5397 = env1 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___289_5397.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___289_5397.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___289_5397.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___289_5397.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___289_5397.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___289_5397.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___289_5397.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___289_5397.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___289_5397.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___289_5397.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___289_5397.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___289_5397.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___289_5397.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___289_5397.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___289_5397.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___289_5397.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___289_5397.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___289_5397.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___289_5397.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___289_5397.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___289_5397.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___289_5397.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___289_5397.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___289_5397.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___289_5397.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___289_5397.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___289_5397.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___289_5397.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___289_5397.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___289_5397.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___289_5397.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___289_5397.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___289_5397.FStar_TypeChecker_Env.dep_graph)
                    }) top in
               match uu____5388 with
               | (lax_top,l,g) ->
                   let lax_top1 =
                     FStar_TypeChecker_Normalize.remove_uvar_solutions env1
                       lax_top in
                   let uu____5408 = FStar_TypeChecker_Env.should_verify env1 in
                   (if uu____5408
                    then
                      let uu____5415 =
                        let uu____5416 = is_lb_unannotated top in
                        if uu____5416 then drop_lbtyp lax_top1 else lax_top1 in
                      check_top_level_let env1 uu____5415
                    else (lax_top1, l, g))
             else check_top_level_let env1 top))
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____5420),uu____5421) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____5436;
                FStar_Syntax_Syntax.lbunivs = uu____5437;
                FStar_Syntax_Syntax.lbtyp = uu____5438;
                FStar_Syntax_Syntax.lbeff = uu____5439;
                FStar_Syntax_Syntax.lbdef = uu____5440;_}::uu____5441),uu____5442)
           ->
           ((let uu____5464 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____5464
             then
               let uu____5465 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____5465
             else ());
            (let uu____5467 = FStar_Options.use_two_phase_tc () in
             if uu____5467
             then
               let uu____5474 =
                 check_top_level_let_rec
                   (let uu___290_5483 = env1 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___290_5483.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___290_5483.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___290_5483.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___290_5483.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___290_5483.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___290_5483.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___290_5483.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___290_5483.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___290_5483.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___290_5483.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___290_5483.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___290_5483.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___290_5483.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___290_5483.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___290_5483.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___290_5483.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___290_5483.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___290_5483.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___290_5483.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___290_5483.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___290_5483.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___290_5483.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___290_5483.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___290_5483.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___290_5483.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___290_5483.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___290_5483.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___290_5483.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___290_5483.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___290_5483.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___290_5483.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___290_5483.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.dep_graph =
                        (uu___290_5483.FStar_TypeChecker_Env.dep_graph)
                    }) top in
               match uu____5474 with
               | (lax_top,l,g) ->
                   let lax_top1 =
                     FStar_TypeChecker_Normalize.remove_uvar_solutions env1
                       lax_top in
                   let uu____5494 = FStar_TypeChecker_Env.should_verify env1 in
                   (if uu____5494
                    then check_top_level_let_rec env1 lax_top1
                    else (lax_top1, l, g))
             else check_top_level_let_rec env1 top))
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____5503),uu____5504) ->
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
        let uu____5530 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5620))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____5680))::(uu____5681,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____5682))::
              (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____5755 ->
              FStar_Exn.raise
                (FStar_Errors.Error ("synth_by_tactic: bad application", rng)) in
        match uu____5530 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____5839 = FStar_TypeChecker_Env.expected_typ env in
                  (match uu____5839 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____5845 =
                         let uu____5846 =
                           let uu____5851 =
                             FStar_TypeChecker_Env.get_range env in
                           ("synth_by_tactic: need a type annotation when no expected type is present",
                             uu____5851) in
                         FStar_Errors.Error uu____5846 in
                       FStar_Exn.raise uu____5845) in
            let uu____5854 = FStar_TypeChecker_Env.clear_expected_typ env in
            (match uu____5854 with
             | (env',uu____5868) ->
                 let uu____5873 = tc_term env' typ in
                 (match uu____5873 with
                  | (typ1,uu____5887,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____5890 = tc_tactic env' tau in
                        match uu____5890 with
                        | (tau1,uu____5904,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let t =
                                if env.FStar_TypeChecker_Env.nosynth
                                then
                                  let uu____5912 =
                                    let uu____5913 =
                                      FStar_TypeChecker_Util.fvar_const env
                                        FStar_Parser_Const.magic_lid in
                                    let uu____5914 =
                                      let uu____5915 =
                                        FStar_Syntax_Syntax.as_arg
                                          FStar_Syntax_Util.exp_unit in
                                      [uu____5915] in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____5913
                                      uu____5914 in
                                  uu____5912 FStar_Pervasives_Native.None rng
                                else
                                  (let t =
                                     env.FStar_TypeChecker_Env.synth env'
                                       typ1 tau1 in
                                   (let uu____5921 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Tac") in
                                    if uu____5921
                                    then
                                      let uu____5922 =
                                        FStar_Syntax_Print.term_to_string t in
                                      FStar_Util.print1 "Got %s\n" uu____5922
                                    else ());
                                   t) in
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____5925 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng in
                               tc_term env uu____5925)))))))
and tc_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___291_5929 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___291_5929.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___291_5929.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___291_5929.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___291_5929.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___291_5929.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___291_5929.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___291_5929.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___291_5929.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___291_5929.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___291_5929.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___291_5929.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___291_5929.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___291_5929.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___291_5929.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___291_5929.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___291_5929.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___291_5929.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___291_5929.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___291_5929.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___291_5929.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___291_5929.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___291_5929.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___291_5929.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___291_5929.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___291_5929.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___291_5929.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___291_5929.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___291_5929.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___291_5929.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___291_5929.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___291_5929.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___291_5929.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___291_5929.FStar_TypeChecker_Env.dep_graph)
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
        let uu___292_5933 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___292_5933.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___292_5933.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___292_5933.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___292_5933.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___292_5933.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___292_5933.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___292_5933.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___292_5933.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___292_5933.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___292_5933.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___292_5933.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___292_5933.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___292_5933.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___292_5933.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___292_5933.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___292_5933.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___292_5933.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___292_5933.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___292_5933.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___292_5933.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___292_5933.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.tc_term =
            (uu___292_5933.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___292_5933.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___292_5933.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___292_5933.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___292_5933.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___292_5933.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___292_5933.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___292_5933.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___292_5933.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___292_5933.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___292_5933.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.dep_graph =
            (uu___292_5933.FStar_TypeChecker_Env.dep_graph)
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
          let uu____5949 = tc_tactic env tactic in
          (match uu____5949 with
           | (tactic1,uu____5959,uu____5960) ->
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
        let uu____5999 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____5999 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____6020 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____6020
              then FStar_Util.Inl t1
              else
                (let uu____6026 =
                   let uu____6027 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____6027 in
                 FStar_Util.Inr uu____6026) in
            let is_data_ctor uu___275_6037 =
              match uu___275_6037 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____6040) -> true
              | uu____6047 -> false in
            let uu____6050 =
              (is_data_ctor dc) &&
                (let uu____6052 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____6052) in
            if uu____6050
            then
              let uu____6059 =
                let uu____6060 =
                  let uu____6065 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____6066 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____6065, uu____6066) in
                FStar_Errors.Error uu____6060 in
              FStar_Exn.raise uu____6059
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____6083 =
            let uu____6084 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____6084 in
          failwith uu____6083
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____6118 =
              let uu____6119 = FStar_Syntax_Subst.compress t1 in
              uu____6119.FStar_Syntax_Syntax.n in
            match uu____6118 with
            | FStar_Syntax_Syntax.Tm_arrow uu____6122 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____6135 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___293_6173 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___293_6173.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___293_6173.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___293_6173.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____6225 =
            let uu____6238 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____6238 with
            | FStar_Pervasives_Native.None  ->
                let uu____6253 = FStar_Syntax_Util.type_u () in
                (match uu____6253 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____6225 with
           | (t,uu____6290,g0) ->
               let uu____6304 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____6304 with
                | (e1,uu____6324,g1) ->
                    let uu____6338 =
                      let uu____6339 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____6339
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____6340 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____6338, uu____6340)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____6342 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____6355 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____6355)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____6342 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___294_6374 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___294_6374.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___294_6374.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____6377 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____6377 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____6398 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____6398
                       then FStar_Util.Inl t1
                       else
                         (let uu____6404 =
                            let uu____6405 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____6405 in
                          FStar_Util.Inr uu____6404) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6411;
             FStar_Syntax_Syntax.vars = uu____6412;_},uu____6413)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____6418 =
            let uu____6419 =
              let uu____6424 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____6424) in
            FStar_Errors.Error uu____6419 in
          FStar_Exn.raise uu____6418
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____6432 =
            let uu____6433 =
              let uu____6438 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____6438) in
            FStar_Errors.Error uu____6433 in
          FStar_Exn.raise uu____6432
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____6446;
             FStar_Syntax_Syntax.vars = uu____6447;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____6456 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6456 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____6479 =
                     let uu____6480 =
                       let uu____6485 =
                         let uu____6486 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____6487 =
                           FStar_Util.string_of_int (FStar_List.length us1) in
                         let uu____6488 =
                           FStar_Util.string_of_int (FStar_List.length us') in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____6486 uu____6487 uu____6488 in
                       let uu____6489 = FStar_TypeChecker_Env.get_range env1 in
                       (uu____6485, uu____6489) in
                     FStar_Errors.Error uu____6480 in
                   FStar_Exn.raise uu____6479)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____6505 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6509 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6509 us1 in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6511 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6511 with
           | ((us,t),range) ->
               ((let uu____6534 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____6534
                 then
                   let uu____6535 =
                     let uu____6536 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____6536 in
                   let uu____6537 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____6538 = FStar_Range.string_of_range range in
                   let uu____6539 = FStar_Range.string_of_use_range range in
                   let uu____6540 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____6535 uu____6537 uu____6538 uu____6539 uu____6540
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____6545 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____6545 us in
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
          let uu____6569 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6569 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____6583 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____6583 with
                | (env2,uu____6597) ->
                    let uu____6602 = tc_binders env2 bs1 in
                    (match uu____6602 with
                     | (bs2,env3,g,us) ->
                         let uu____6621 = tc_comp env3 c1 in
                         (match uu____6621 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___295_6640 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___295_6640.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___295_6640.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____6649 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____6649 in
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
          let uu____6668 =
            let uu____6673 =
              let uu____6674 = FStar_Syntax_Syntax.mk_binder x in
              [uu____6674] in
            FStar_Syntax_Subst.open_term uu____6673 phi in
          (match uu____6668 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____6684 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____6684 with
                | (env2,uu____6698) ->
                    let uu____6703 =
                      let uu____6716 = FStar_List.hd x1 in
                      tc_binder env2 uu____6716 in
                    (match uu____6703 with
                     | (x2,env3,f1,u) ->
                         ((let uu____6744 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____6744
                           then
                             let uu____6745 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____6746 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____6747 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____6745 uu____6746 uu____6747
                           else ());
                          (let uu____6749 = FStar_Syntax_Util.type_u () in
                           match uu____6749 with
                           | (t_phi,uu____6761) ->
                               let uu____6762 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____6762 with
                                | (phi2,uu____6776,f2) ->
                                    let e1 =
                                      let uu___296_6781 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___296_6781.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___296_6781.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____6788 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____6788 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____6801) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____6824 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____6824
            then
              let uu____6825 =
                FStar_Syntax_Print.term_to_string
                  (let uu___297_6828 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___297_6828.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___297_6828.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____6825
            else ());
           (let uu____6834 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____6834 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____6847 ->
          let uu____6848 =
            let uu____6849 = FStar_Syntax_Print.term_to_string top in
            let uu____6850 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____6849
              uu____6850 in
          failwith uu____6848
and tc_constant:
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____6860 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____6861,FStar_Pervasives_Native.None ) ->
            FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____6872,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____6888 -> FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_float uu____6893 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____6894 ->
            let uu____6895 =
              let uu____6900 =
                FStar_ToSyntax_Env.try_lookup_lid
                  env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid in
              FStar_All.pipe_right uu____6900 FStar_Util.must in
            FStar_All.pipe_right uu____6895 FStar_Pervasives_Native.fst
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____6925 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____6926 =
              let uu____6927 =
                let uu____6932 =
                  let uu____6933 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____6933 in
                (uu____6932, r) in
              FStar_Errors.Error uu____6927 in
            FStar_Exn.raise uu____6926
        | FStar_Const.Const_set_range_of  ->
            let uu____6934 =
              let uu____6935 =
                let uu____6940 =
                  let uu____6941 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____6941 in
                (uu____6940, r) in
              FStar_Errors.Error uu____6935 in
            FStar_Exn.raise uu____6934
        | FStar_Const.Const_reify  ->
            let uu____6942 =
              let uu____6943 =
                let uu____6948 =
                  let uu____6949 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____6949 in
                (uu____6948, r) in
              FStar_Errors.Error uu____6943 in
            FStar_Exn.raise uu____6942
        | FStar_Const.Const_reflect uu____6950 ->
            let uu____6951 =
              let uu____6952 =
                let uu____6957 =
                  let uu____6958 = FStar_Parser_Const.const_to_string c in
                  FStar_Util.format1
                    "Ill-typed %s: this constant must be fully applied"
                    uu____6958 in
                (uu____6957, r) in
              FStar_Errors.Error uu____6952 in
            FStar_Exn.raise uu____6951
        | uu____6959 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____6976) ->
          let uu____6985 = FStar_Syntax_Util.type_u () in
          (match uu____6985 with
           | (k,u) ->
               let uu____6998 = tc_check_tot_or_gtot_term env t k in
               (match uu____6998 with
                | (t1,uu____7012,g) ->
                    let uu____7014 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____7014, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____7016) ->
          let uu____7025 = FStar_Syntax_Util.type_u () in
          (match uu____7025 with
           | (k,u) ->
               let uu____7038 = tc_check_tot_or_gtot_term env t k in
               (match uu____7038 with
                | (t1,uu____7052,g) ->
                    let uu____7054 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____7054, u, g)))
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
            let uu____7062 =
              let uu____7063 =
                let uu____7064 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____7064 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____7063 in
            uu____7062 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____7067 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____7067 with
           | (tc1,uu____7081,f) ->
               let uu____7083 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____7083 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____7127 =
                        let uu____7128 = FStar_Syntax_Subst.compress head3 in
                        uu____7128.FStar_Syntax_Syntax.n in
                      match uu____7127 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____7131,us) -> us
                      | uu____7137 -> [] in
                    let uu____7138 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____7138 with
                     | (uu____7159,args1) ->
                         let uu____7181 =
                           let uu____7200 = FStar_List.hd args1 in
                           let uu____7213 = FStar_List.tl args1 in
                           (uu____7200, uu____7213) in
                         (match uu____7181 with
                          | (res,args2) ->
                              let uu____7278 =
                                let uu____7287 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___276_7315  ->
                                          match uu___276_7315 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____7323 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____7323 with
                                               | (env1,uu____7335) ->
                                                   let uu____7340 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____7340 with
                                                    | (e1,uu____7352,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____7287
                                  FStar_List.unzip in
                              (match uu____7278 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___298_7391 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___298_7391.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___298_7391.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____7395 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____7395 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____7399 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____7399))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____7407 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____7408 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____7418 = aux u3 in FStar_Syntax_Syntax.U_succ uu____7418
        | FStar_Syntax_Syntax.U_max us ->
            let uu____7422 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____7422
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____7427 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____7427 FStar_Pervasives_Native.snd
         | uu____7436 -> aux u)
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
            let uu____7460 =
              let uu____7461 =
                let uu____7466 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____7466, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____7461 in
            FStar_Exn.raise uu____7460 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____7556 bs2 bs_expected1 =
              match uu____7556 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____7724)) ->
                             let uu____7729 =
                               let uu____7730 =
                                 let uu____7735 =
                                   let uu____7736 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____7736 in
                                 let uu____7737 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____7735, uu____7737) in
                               FStar_Errors.Error uu____7730 in
                             FStar_Exn.raise uu____7729
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____7738),FStar_Pervasives_Native.None ) ->
                             let uu____7743 =
                               let uu____7744 =
                                 let uu____7749 =
                                   let uu____7750 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____7750 in
                                 let uu____7751 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____7749, uu____7751) in
                               FStar_Errors.Error uu____7744 in
                             FStar_Exn.raise uu____7743
                         | uu____7752 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____7758 =
                           let uu____7763 =
                             let uu____7764 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____7764.FStar_Syntax_Syntax.n in
                           match uu____7763 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____7771 ->
                               ((let uu____7773 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____7773
                                 then
                                   let uu____7774 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____7774
                                 else ());
                                (let uu____7776 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____7776 with
                                 | (t,uu____7788,g1) ->
                                     let g2 =
                                       let uu____7791 =
                                         FStar_TypeChecker_Rel.teq_nosmt env2
                                           t expected_t in
                                       if uu____7791
                                       then
                                         FStar_TypeChecker_Rel.trivial_guard
                                       else
                                         (let uu____7793 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t in
                                          match uu____7793 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____7796 =
                                                let uu____7797 =
                                                  let uu____7802 =
                                                    FStar_TypeChecker_Err.basic_type_error
                                                      env2
                                                      FStar_Pervasives_Native.None
                                                      expected_t t in
                                                  let uu____7803 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env2 in
                                                  (uu____7802, uu____7803) in
                                                FStar_Errors.Error uu____7797 in
                                              FStar_Exn.raise uu____7796
                                          | FStar_Pervasives_Native.Some g2
                                              ->
                                              let uu____7805 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2 in
                                              FStar_TypeChecker_Util.label_guard
                                                uu____7805
                                                "Type annotation on parameter incompatible with the expected type"
                                                g2) in
                                     let g3 =
                                       let uu____7807 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____7807 in
                                     (t, g3))) in
                         match uu____7758 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___299_7835 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___299_7835.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___299_7835.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____7848 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____7848 in
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
                  | uu____7996 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____8005 = tc_binders env1 bs in
                  match uu____8005 with
                  | (bs1,envbody,g,uu____8035) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____8079 =
                    let uu____8080 = FStar_Syntax_Subst.compress t2 in
                    uu____8080.FStar_Syntax_Syntax.n in
                  match uu____8079 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____8103 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8127 -> failwith "Impossible");
                       (let uu____8136 = tc_binders env1 bs in
                        match uu____8136 with
                        | (bs1,envbody,g,uu____8168) ->
                            let uu____8169 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____8169 with
                             | (envbody1,uu____8197) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____8208;
                         FStar_Syntax_Syntax.pos = uu____8209;
                         FStar_Syntax_Syntax.vars = uu____8210;_},uu____8211)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____8255 -> failwith "Impossible");
                       (let uu____8264 = tc_binders env1 bs in
                        match uu____8264 with
                        | (bs1,envbody,g,uu____8296) ->
                            let uu____8297 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____8297 with
                             | (envbody1,uu____8325) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____8337) ->
                      let uu____8342 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____8342 with
                       | (uu____8383,bs1,bs',copt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____8426 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____8426 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____8535 c_expected2 body3
                               =
                               match uu____8535 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____8655 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____8655, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____8686 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____8686 in
                                        let uu____8687 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____8687, body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        let uu____8712 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c) in
                                        if uu____8712
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
                                               let uu____8764 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____8764 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____8787 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____8787 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____8837 =
                                                           let uu____8868 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____8868,
                                                             subst2) in
                                                         handle_more
                                                           uu____8837
                                                           c_expected4 body3))
                                           | uu____8885 ->
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
                             let uu____8901 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____8901 c_expected1 body2 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___300_8962 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___300_8962.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___300_8962.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___300_8962.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___300_8962.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___300_8962.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___300_8962.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___300_8962.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___300_8962.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___300_8962.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___300_8962.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___300_8962.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___300_8962.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___300_8962.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___300_8962.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___300_8962.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___300_8962.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___300_8962.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___300_8962.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___300_8962.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___300_8962.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___300_8962.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___300_8962.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___300_8962.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___300_8962.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___300_8962.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___300_8962.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___300_8962.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___300_8962.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___300_8962.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___300_8962.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___300_8962.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___300_8962.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___300_8962.FStar_TypeChecker_Env.dep_graph)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____9010  ->
                                     fun uu____9011  ->
                                       match (uu____9010, uu____9011) with
                                       | ((env2,letrec_binders),(l,t3,u_names))
                                           ->
                                           let uu____9073 =
                                             let uu____9080 =
                                               let uu____9081 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____9081
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____9080 t3 in
                                           (match uu____9073 with
                                            | (t4,uu____9103,uu____9104) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (u_names, t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____9114 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___301_9117
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___301_9117.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___301_9117.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____9114 ::
                                                        letrec_binders
                                                  | uu____9118 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____9123 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1 in
                           (match uu____9123 with
                            | (envbody,bs1,g,c,body2) ->
                                let uu____9177 = mk_letrec_env envbody bs1 c in
                                (match uu____9177 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, g))))
                  | uu____9223 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____9244 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____9244
                      else
                        (let uu____9246 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1 in
                         match uu____9246 with
                         | (uu____9285,bs1,uu____9287,c_opt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____9307 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____9307 with
          | (env1,topt) ->
              ((let uu____9327 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____9327
                then
                  let uu____9328 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____9328
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____9332 = expected_function_typ1 env1 topt body in
                match uu____9332 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let uu____9372 =
                      let should_check_expected_effect =
                        let uu____9380 =
                          let uu____9387 =
                            let uu____9388 =
                              FStar_Syntax_Subst.compress body1 in
                            uu____9388.FStar_Syntax_Syntax.n in
                          (c_opt, uu____9387) in
                        match uu____9380 with
                        | (FStar_Pervasives_Native.None
                           ,FStar_Syntax_Syntax.Tm_ascribed
                           (uu____9393,(FStar_Util.Inr expected_c,uu____9395),uu____9396))
                            -> false
                        | uu____9445 -> true in
                      let uu____9452 =
                        tc_term
                          (let uu___302_9461 = envbody in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___302_9461.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___302_9461.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___302_9461.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___302_9461.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___302_9461.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___302_9461.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___302_9461.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___302_9461.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___302_9461.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___302_9461.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___302_9461.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___302_9461.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___302_9461.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = false;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___302_9461.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq = use_eq;
                             FStar_TypeChecker_Env.is_iface =
                               (uu___302_9461.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___302_9461.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___302_9461.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___302_9461.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.failhard =
                               (uu___302_9461.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___302_9461.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___302_9461.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___302_9461.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___302_9461.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___302_9461.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qname_and_index =
                               (uu___302_9461.FStar_TypeChecker_Env.qname_and_index);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___302_9461.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth =
                               (uu___302_9461.FStar_TypeChecker_Env.synth);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___302_9461.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___302_9461.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___302_9461.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___302_9461.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.dep_graph =
                               (uu___302_9461.FStar_TypeChecker_Env.dep_graph)
                           }) body1 in
                      match uu____9452 with
                      | (body2,cbody,guard_body) ->
                          let guard_body1 =
                            FStar_TypeChecker_Rel.solve_deferred_constraints
                              envbody guard_body in
                          if should_check_expected_effect
                          then
                            let uu____9478 =
                              let uu____9485 =
                                let uu____9490 =
                                  cbody.FStar_Syntax_Syntax.comp () in
                                (body2, uu____9490) in
                              check_expected_effect
                                (let uu___303_9497 = envbody in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___303_9497.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___303_9497.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___303_9497.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___303_9497.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___303_9497.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___303_9497.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___303_9497.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___303_9497.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___303_9497.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___303_9497.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___303_9497.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___303_9497.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___303_9497.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___303_9497.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___303_9497.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq = use_eq;
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___303_9497.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___303_9497.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___303_9497.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___303_9497.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___303_9497.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___303_9497.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___303_9497.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___303_9497.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___303_9497.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___303_9497.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___303_9497.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___303_9497.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___303_9497.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___303_9497.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___303_9497.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___303_9497.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___303_9497.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___303_9497.FStar_TypeChecker_Env.dep_graph)
                                 }) c_opt uu____9485 in
                            (match uu____9478 with
                             | (body3,cbody1,guard) ->
                                 let uu____9507 =
                                   FStar_TypeChecker_Rel.conj_guard
                                     guard_body1 guard in
                                 (body3, cbody1, uu____9507))
                          else
                            (let uu____9509 =
                               cbody.FStar_Syntax_Syntax.comp () in
                             (body2, uu____9509, guard_body1)) in
                    (match uu____9372 with
                     | (body2,cbody,guard) ->
                         let guard1 =
                           let uu____9524 =
                             env1.FStar_TypeChecker_Env.top_level ||
                               (let uu____9526 =
                                  FStar_TypeChecker_Env.should_verify env1 in
                                Prims.op_Negation uu____9526) in
                           if uu____9524
                           then
                             let uu____9527 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             FStar_TypeChecker_Rel.discharge_guard envbody
                               uu____9527
                           else
                             (let guard1 =
                                let uu____9530 =
                                  FStar_TypeChecker_Rel.conj_guard g guard in
                                FStar_TypeChecker_Rel.close_guard env1
                                  (FStar_List.append bs1 letrec_binders)
                                  uu____9530 in
                              guard1) in
                         let tfun_computed =
                           FStar_Syntax_Util.arrow bs1 cbody in
                         let e =
                           FStar_Syntax_Util.abs bs1 body2
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_comp_of_comp
                                   (FStar_Util.dflt cbody c_opt))) in
                         let uu____9539 =
                           match tfun_opt with
                           | FStar_Pervasives_Native.Some t ->
                               let t1 = FStar_Syntax_Subst.compress t in
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_arrow uu____9560 ->
                                    (e, t1, guard1)
                                | uu____9573 ->
                                    let uu____9574 =
                                      FStar_TypeChecker_Util.check_and_ascribe
                                        env1 e tfun_computed t1 in
                                    (match uu____9574 with
                                     | (e1,guard') ->
                                         let uu____9587 =
                                           FStar_TypeChecker_Rel.conj_guard
                                             guard1 guard' in
                                         (e1, t1, uu____9587)))
                           | FStar_Pervasives_Native.None  ->
                               (e, tfun_computed, guard1) in
                         (match uu____9539 with
                          | (e1,tfun,guard2) ->
                              let c =
                                if env1.FStar_TypeChecker_Env.top_level
                                then FStar_Syntax_Syntax.mk_Total tfun
                                else
                                  FStar_TypeChecker_Util.return_value env1
                                    tfun e1 in
                              let uu____9601 =
                                FStar_TypeChecker_Util.strengthen_precondition
                                  FStar_Pervasives_Native.None env1 e1
                                  (FStar_Syntax_Util.lcomp_of_comp c) guard2 in
                              (match uu____9601 with
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
              (let uu____9650 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____9650
               then
                 let uu____9651 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____9652 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____9651
                   uu____9652
               else ());
              (let monadic_application uu____9709 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____9709 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___304_9768 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___304_9768.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___304_9768.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___304_9768.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____9769 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
                       | uu____9784 ->
                           let g =
                             let uu____9792 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____9792
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____9793 =
                             let uu____9794 =
                               let uu____9797 =
                                 let uu____9798 =
                                   let uu____9799 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____9799 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____9798 in
                               FStar_Syntax_Syntax.mk_Total uu____9797 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____9794 in
                           (uu____9793, g) in
                     (match uu____9769 with
                      | (cres2,guard1) ->
                          ((let uu____9813 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____9813
                            then
                              let uu____9814 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____9814
                            else ());
                           (let cres3 =
                              let uu____9817 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____9817
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
                                   fun uu____9851  ->
                                     match uu____9851 with
                                     | ((e,q),x,c) ->
                                         let uu____9884 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____9884
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
                              let uu____9896 =
                                let uu____9897 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____9897.FStar_Syntax_Syntax.n in
                              match uu____9896 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____9901 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____9922  ->
                                         match uu____9922 with
                                         | (arg,uu____9936,uu____9937) -> arg
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
                                (let uu____9947 =
                                   let map_fun uu____10009 =
                                     match uu____10009 with
                                     | ((e,q),uu____10044,c) ->
                                         let uu____10054 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____10054
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
                                            let uu____10104 =
                                              let uu____10109 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____10109, q) in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____10104)) in
                                   let uu____10138 =
                                     let uu____10163 =
                                       let uu____10186 =
                                         let uu____10201 =
                                           let uu____10210 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____10210,
                                             FStar_Pervasives_Native.None,
                                             chead1) in
                                         uu____10201 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____10186 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____10163 in
                                   match uu____10138 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____10383 =
                                         let uu____10384 =
                                           FStar_List.hd reverse_args in
                                         FStar_Pervasives_Native.fst
                                           uu____10384 in
                                       let uu____10393 =
                                         let uu____10400 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____10400 in
                                       (lifted_args, uu____10383,
                                         uu____10393) in
                                 match uu____9947 with
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
                                     let bind_lifted_args e uu___277_10503 =
                                       match uu___277_10503 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____10558 =
                                               let uu____10561 =
                                                 let uu____10562 =
                                                   let uu____10575 =
                                                     let uu____10576 =
                                                       let uu____10577 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____10577] in
                                                     FStar_Syntax_Subst.close
                                                       uu____10576 e in
                                                   ((false, [lb]),
                                                     uu____10575) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____10562 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10561 in
                                             uu____10558
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
                            let uu____10607 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp1
                                guard1 in
                            match uu____10607 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____10698 bs args1 =
                 match uu____10698 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____10845))::rest,
                         (uu____10847,FStar_Pervasives_Native.None )::uu____10848)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t in
                          let uu____10909 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____10909 with
                           | (varg,uu____10929,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____10951 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____10951) in
                               let uu____10952 =
                                 let uu____10987 =
                                   let uu____11002 =
                                     let uu____11015 =
                                       let uu____11016 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____11016
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____11015) in
                                   uu____11002 :: outargs in
                                 let uu____11035 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____10987, (arg :: arg_rets),
                                   uu____11035, fvs) in
                               tc_args head_info uu____10952 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____11137),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11138)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____11151 ->
                                FStar_Exn.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___305_11162 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___305_11162.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___305_11162.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____11164 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____11164
                             then
                               let uu____11165 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____11165
                             else ());
                            (let targ1 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___306_11170 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___306_11170.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___306_11170.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___306_11170.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___306_11170.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___306_11170.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___306_11170.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___306_11170.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___306_11170.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___306_11170.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___306_11170.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___306_11170.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___306_11170.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___306_11170.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___306_11170.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___306_11170.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___306_11170.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___306_11170.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___306_11170.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___306_11170.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___306_11170.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___306_11170.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___306_11170.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___306_11170.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___306_11170.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___306_11170.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___306_11170.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___306_11170.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___306_11170.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___306_11170.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___306_11170.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___306_11170.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___306_11170.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___306_11170.FStar_TypeChecker_Env.dep_graph)
                               } in
                             (let uu____11172 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____11172
                              then
                                let uu____11173 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____11174 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11175 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____11173 uu____11174 uu____11175
                              else ());
                             (let uu____11177 = tc_term env2 e in
                              match uu____11177 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____11204 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____11204 in
                                  let uu____11205 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____11205
                                  then
                                    let subst2 =
                                      let uu____11213 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____11213
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
                      | (uu____11307,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____11343) ->
                          let uu____11394 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____11394 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____11428 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____11428
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____11453 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____11453 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____11476 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____11476
                                            then
                                              FStar_Errors.warn
                                                tres1.FStar_Syntax_Syntax.pos
                                                "Potentially redundant explicit currying of a function type"
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____11518 when Prims.op_Negation norm1
                                     ->
                                     let uu____11519 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____11519
                                 | uu____11520 ->
                                     let uu____11521 =
                                       let uu____11522 =
                                         let uu____11527 =
                                           let uu____11528 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____11529 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____11528 uu____11529 in
                                         let uu____11536 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____11527, uu____11536) in
                                       FStar_Errors.Error uu____11522 in
                                     FStar_Exn.raise uu____11521 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____11555 =
                   let uu____11556 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____11556.FStar_Syntax_Syntax.n in
                 match uu____11555 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____11567 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____11668 = tc_term env1 e in
                           (match uu____11668 with
                            | (e1,c,g_e) ->
                                let uu____11690 = tc_args1 env1 tl1 in
                                (match uu____11690 with
                                 | (args2,comps,g_rest) ->
                                     let uu____11730 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____11730))) in
                     let uu____11751 = tc_args1 env args in
                     (match uu____11751 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____11788 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____11826  ->
                                      match uu____11826 with
                                      | (uu____11839,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____11788 in
                          let ml_or_tot t r1 =
                            let uu____11856 = FStar_Options.ml_ish () in
                            if uu____11856
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____11859 =
                              let uu____11862 =
                                let uu____11863 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____11863
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____11862 in
                            ml_or_tot uu____11859 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____11876 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____11876
                            then
                              let uu____11877 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____11878 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____11879 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____11877 uu____11878 uu____11879
                            else ());
                           (let uu____11882 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____11882);
                           (let comp =
                              let uu____11884 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____11895  ->
                                   fun out  ->
                                     match uu____11895 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____11884 in
                            let uu____11909 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____11912 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____11909, comp, uu____11912))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____11915;
                        FStar_Syntax_Syntax.pos = uu____11916;
                        FStar_Syntax_Syntax.vars = uu____11917;_},uu____11918)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____12039 = tc_term env1 e in
                           (match uu____12039 with
                            | (e1,c,g_e) ->
                                let uu____12061 = tc_args1 env1 tl1 in
                                (match uu____12061 with
                                 | (args2,comps,g_rest) ->
                                     let uu____12101 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____12101))) in
                     let uu____12122 = tc_args1 env args in
                     (match uu____12122 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____12159 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____12197  ->
                                      match uu____12197 with
                                      | (uu____12210,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____12159 in
                          let ml_or_tot t r1 =
                            let uu____12227 = FStar_Options.ml_ish () in
                            if uu____12227
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____12230 =
                              let uu____12233 =
                                let uu____12234 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____12234
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____12233 in
                            ml_or_tot uu____12230 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____12247 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____12247
                            then
                              let uu____12248 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____12249 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____12250 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____12248 uu____12249 uu____12250
                            else ());
                           (let uu____12253 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____12253);
                           (let comp =
                              let uu____12255 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____12266  ->
                                   fun out  ->
                                     match uu____12266 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____12255 in
                            let uu____12280 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____12283 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____12280, comp, uu____12283))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____12304 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____12304 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____12369) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____12375,uu____12376) -> check_function_app t
                 | uu____12417 ->
                     let uu____12418 =
                       let uu____12419 =
                         let uu____12424 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____12424, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____12419 in
                     FStar_Exn.raise uu____12418 in
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
                  let uu____12494 =
                    FStar_List.fold_left2
                      (fun uu____12537  ->
                         fun uu____12538  ->
                           fun uu____12539  ->
                             match (uu____12537, uu____12538, uu____12539)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Exn.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____12607 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____12607 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____12625 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____12625 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____12629 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____12629)
                                              &&
                                              (let uu____12631 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____12631)) in
                                       let uu____12632 =
                                         let uu____12641 =
                                           let uu____12650 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____12650] in
                                         FStar_List.append seen uu____12641 in
                                       let uu____12657 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____12632, uu____12657, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____12494 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r in
                       let c1 =
                         if ghost
                         then
                           let uu____12693 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____12693
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____12695 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____12695 with | (c2,g) -> (e, c2, g)))
              | uu____12712 ->
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
        let uu____12746 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____12746 with
        | (pattern,when_clause,branch_exp) ->
            let uu____12782 = branch1 in
            (match uu____12782 with
             | (cpat,uu____12814,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let tc_annot env1 t =
                     let uu____12881 = FStar_Syntax_Util.type_u () in
                     match uu____12881 with
                     | (tu,u) ->
                         let uu____12892 =
                           tc_check_tot_or_gtot_term env1 t tu in
                         (match uu____12892 with
                          | (t1,uu____12904,g) -> (t1, g)) in
                   let uu____12906 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0
                       tc_annot in
                   match uu____12906 with
                   | (pat_bvs1,exp,guard_pat_annots,p) ->
                       ((let uu____12940 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____12940
                         then
                           let uu____12941 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____12942 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____12941 uu____12942
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____12945 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____12945 with
                         | (env1,uu____12967) ->
                             let env11 =
                               let uu___307_12973 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___307_12973.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___307_12973.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___307_12973.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___307_12973.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___307_12973.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___307_12973.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___307_12973.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___307_12973.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___307_12973.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___307_12973.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___307_12973.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___307_12973.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___307_12973.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___307_12973.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___307_12973.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___307_12973.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___307_12973.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___307_12973.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___307_12973.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___307_12973.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___307_12973.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___307_12973.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___307_12973.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___307_12973.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___307_12973.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___307_12973.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___307_12973.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___307_12973.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___307_12973.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___307_12973.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___307_12973.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___307_12973.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___307_12973.FStar_TypeChecker_Env.dep_graph)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____12976 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____12976
                               then
                                 let uu____12977 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____12978 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____12977 uu____12978
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t in
                               let uu____12981 =
                                 tc_tot_or_gtot_term env12 exp in
                               match uu____12981 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___308_13006 = g in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___308_13006.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___308_13006.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___308_13006.FStar_TypeChecker_Env.implicits)
                                     } in
                                   let uu____13007 =
                                     let uu____13008 =
                                       FStar_TypeChecker_Rel.teq_nosmt env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t in
                                     if uu____13008
                                     then
                                       let env13 =
                                         FStar_TypeChecker_Env.set_range
                                           env12 exp1.FStar_Syntax_Syntax.pos in
                                       let uu____13010 =
                                         FStar_TypeChecker_Rel.discharge_guard_no_smt
                                           env13 g1 in
                                       FStar_All.pipe_right uu____13010
                                         FStar_TypeChecker_Rel.resolve_implicits
                                     else
                                       (let uu____13012 =
                                          let uu____13013 =
                                            let uu____13018 =
                                              let uu____13019 =
                                                FStar_Syntax_Print.term_to_string
                                                  lc.FStar_Syntax_Syntax.res_typ in
                                              let uu____13020 =
                                                FStar_Syntax_Print.term_to_string
                                                  expected_pat_t in
                                              FStar_Util.format2
                                                "Inferred type of pattern (%s) is incompatible with the type of the scrutinee (%s)"
                                                uu____13019 uu____13020 in
                                            (uu____13018,
                                              (exp1.FStar_Syntax_Syntax.pos)) in
                                          FStar_Errors.Error uu____13013 in
                                        FStar_Exn.raise uu____13012) in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1 in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____13037 =
                                       let uu____13038 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____13038 in
                                     if uu____13037
                                     then
                                       let unresolved =
                                         let uu____13050 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____13050
                                           FStar_Util.set_elements in
                                       let uu____13077 =
                                         let uu____13078 =
                                           let uu____13083 =
                                             let uu____13084 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____13085 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____13086 =
                                               let uu____13087 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____13105  ->
                                                         match uu____13105
                                                         with
                                                         | (u,uu____13111) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____13087
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____13084 uu____13085
                                               uu____13086 in
                                           (uu____13083,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____13078 in
                                       FStar_Exn.raise uu____13077
                                     else ());
                                    (let uu____13116 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____13116
                                     then
                                       let uu____13117 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____13117
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1,
                                       guard_pat_annots, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____13126 =
                   let uu____13133 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____13133
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____13126 with
                  | (scrutinee_env,uu____13157) ->
                      let uu____13162 = tc_pat true pat_t pattern in
                      (match uu____13162 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,guard_pat_annots,norm_pat_exp)
                           ->
                           let uu____13203 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____13225 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____13225
                                 then
                                   FStar_Exn.raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____13239 =
                                      let uu____13246 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool in
                                      tc_term uu____13246 e in
                                    match uu____13239 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g)) in
                           (match uu____13203 with
                            | (when_clause1,g_when) ->
                                let uu____13280 = tc_term pat_env branch_exp in
                                (match uu____13280 with
                                 | (branch_exp1,c,g_branch) ->
                                     let g_branch1 =
                                       FStar_TypeChecker_Rel.conj_guard
                                         guard_pat_annots g_branch in
                                     let when_condition =
                                       match when_clause1 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some w ->
                                           let uu____13313 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_41  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_41) uu____13313 in
                                     let uu____13316 =
                                       let eqs =
                                         let uu____13326 =
                                           let uu____13327 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____13327 in
                                         if uu____13326
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____13334 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____13351 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____13352 ->
                                                FStar_Pervasives_Native.None
                                            | uu____13353 ->
                                                let uu____13354 =
                                                  let uu____13355 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____13355 pat_t
                                                    scrutinee_tm e in
                                                FStar_Pervasives_Native.Some
                                                  uu____13354) in
                                       let uu____13356 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch1 in
                                       match uu____13356 with
                                       | (c1,g_branch2) ->
                                           let uu____13371 =
                                             match (eqs, when_condition) with
                                             | uu____13384 when
                                                 let uu____13393 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation
                                                   uu____13393
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
                                                 let uu____13405 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____13406 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____13405, uu____13406)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____13415 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____13415 in
                                                 let uu____13416 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____13417 =
                                                   let uu____13418 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____13418 g_when in
                                                 (uu____13416, uu____13417)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____13426 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____13426, g_when) in
                                           (match uu____13371 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____13438 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____13439 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____13438, uu____13439,
                                                  g_branch2)) in
                                     (match uu____13316 with
                                      | (c1,g_when1,g_branch2) ->
                                          let branch_guard =
                                            let uu____13460 =
                                              let uu____13461 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____13461 in
                                            if uu____13460
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____13491 =
                                                     let uu____13492 =
                                                       let uu____13493 =
                                                         let uu____13496 =
                                                           let uu____13503 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____13503 in
                                                         FStar_Pervasives_Native.snd
                                                           uu____13496 in
                                                       FStar_List.length
                                                         uu____13493 in
                                                     uu____13492 >
                                                       (Prims.parse_int "1") in
                                                   if uu____13491
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____13509 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____13509 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____13530 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None in
                                                         let disc1 =
                                                           let uu____13545 =
                                                             let uu____13546
                                                               =
                                                               let uu____13547
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____13547] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____13546 in
                                                           uu____13545
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____13550 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool in
                                                         [uu____13550]
                                                   else [] in
                                                 let fail uu____13555 =
                                                   let uu____13556 =
                                                     let uu____13557 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____13558 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____13559 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____13557
                                                       uu____13558
                                                       uu____13559 in
                                                   failwith uu____13556 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____13570) ->
                                                       head_constructor t1
                                                   | uu____13575 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____13577 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____13577
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____13580 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____13597;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____13598;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____13599;_},uu____13600)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____13637 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____13639 =
                                                       let uu____13640 =
                                                         tc_constant env
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____13640
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____13639]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____13641 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____13649 =
                                                       let uu____13650 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____13650 in
                                                     if uu____13649
                                                     then []
                                                     else
                                                       (let uu____13654 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13654)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____13657 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____13659 =
                                                       let uu____13660 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____13660 in
                                                     if uu____13659
                                                     then []
                                                     else
                                                       (let uu____13664 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____13664)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____13690 =
                                                       let uu____13691 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____13691 in
                                                     if uu____13690
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____13698 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____13730
                                                                     ->
                                                                    match uu____13730
                                                                    with
                                                                    | 
                                                                    (ei,uu____13740)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____13746
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____13746
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____13767
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____13781
                                                                    =
                                                                    let uu____13782
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____13783
                                                                    =
                                                                    let uu____13784
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____13784] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____13782
                                                                    uu____13783 in
                                                                    uu____13781
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____13698
                                                            FStar_List.flatten in
                                                        let uu____13793 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____13793
                                                          sub_term_guards)
                                                 | uu____13796 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____13808 =
                                                   let uu____13809 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____13809 in
                                                 if uu____13808
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____13812 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____13812 in
                                                    let uu____13817 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____13817 with
                                                    | (k,uu____13823) ->
                                                        let uu____13824 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____13824
                                                         with
                                                         | (t1,uu____13832,uu____13833)
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
                                          ((let uu____13839 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____13839
                                            then
                                              let uu____13840 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____13840
                                            else ());
                                           (let uu____13842 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____13842, branch_guard, c1,
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
          let uu____13868 = check_let_bound_def true env1 lb in
          (match uu____13868 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____13890 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____13907 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____13907, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____13910 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____13910
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____13914 =
                      let uu____13927 =
                        let uu____13942 =
                          let uu____13951 =
                            let uu____13964 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____13964) in
                          [uu____13951] in
                        FStar_TypeChecker_Util.generalize env1 false
                          uu____13942 in
                      FStar_List.hd uu____13927 in
                    match uu____13914 with
                    | (uu____14017,univs1,e11,c11,gvs) ->
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
               (match uu____13890 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____14040 =
                      let uu____14047 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____14047
                      then
                        let uu____14054 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____14054 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____14077 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____14077
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____14078 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____14078, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____14088 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____14088
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm] env1) in
                          let e21 =
                            let uu____14096 =
                              FStar_Syntax_Util.is_pure_comp c in
                            if uu____14096
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
                    (match uu____14040 with
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
                         let uu____14120 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         (uu____14120,
                           (FStar_Syntax_Util.lcomp_of_comp cres),
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____14135 -> failwith "Impossible"
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
            let uu___309_14166 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___309_14166.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___309_14166.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___309_14166.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___309_14166.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___309_14166.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___309_14166.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___309_14166.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___309_14166.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___309_14166.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___309_14166.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___309_14166.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___309_14166.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___309_14166.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___309_14166.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___309_14166.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___309_14166.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___309_14166.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___309_14166.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___309_14166.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___309_14166.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___309_14166.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___309_14166.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___309_14166.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___309_14166.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___309_14166.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___309_14166.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___309_14166.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___309_14166.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___309_14166.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___309_14166.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___309_14166.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___309_14166.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___309_14166.FStar_TypeChecker_Env.dep_graph)
            } in
          let uu____14167 =
            let uu____14178 =
              let uu____14179 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____14179 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____14178 lb in
          (match uu____14167 with
           | (e1,uu____14201,c1,g1,annotated) ->
               let x =
                 let uu___310_14206 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___310_14206.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___310_14206.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____14207 =
                 let uu____14212 =
                   let uu____14213 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____14213] in
                 FStar_Syntax_Subst.open_term uu____14212 e2 in
               (match uu____14207 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = FStar_Pervasives_Native.fst xbinder in
                    let uu____14232 =
                      let uu____14239 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____14239 e21 in
                    (match uu____14232 with
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
                           let uu____14258 =
                             let uu____14261 =
                               let uu____14262 =
                                 let uu____14275 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____14275) in
                               FStar_Syntax_Syntax.Tm_let uu____14262 in
                             FStar_Syntax_Syntax.mk uu____14261 in
                           uu____14258 FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____14289 =
                             let uu____14290 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____14291 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____14290
                               c1.FStar_Syntax_Syntax.res_typ uu____14291 e11 in
                           FStar_All.pipe_left
                             (fun _0_42  ->
                                FStar_TypeChecker_Common.NonTrivial _0_42)
                             uu____14289 in
                         let g21 =
                           let uu____14293 =
                             let uu____14294 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____14294 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____14293 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____14296 =
                           let uu____14297 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____14297 in
                         if uu____14296
                         then
                           let tt =
                             let uu____14307 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____14307
                               FStar_Option.get in
                           ((let uu____14313 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____14313
                             then
                               let uu____14314 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____14315 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____14314 uu____14315
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape FStar_Pervasives_Native.None
                                env2 [x1] cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____14320 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____14320
                             then
                               let uu____14321 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____14322 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____14321 uu____14322
                             else ());
                            (e4,
                              ((let uu___311_14325 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___311_14325.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___311_14325.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___311_14325.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____14326 -> failwith "Impossible"
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
          let uu____14358 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____14358 with
           | (lbs1,e21) ->
               let uu____14377 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____14377 with
                | (env0,topt) ->
                    let uu____14396 = build_let_rec_env true env0 lbs1 in
                    (match uu____14396 with
                     | (lbs2,rec_env) ->
                         let uu____14415 = check_let_recs rec_env lbs2 in
                         (match uu____14415 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____14435 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____14435
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____14441 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____14441
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
                                     let uu____14490 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____14530 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____14530))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____14490 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____14579  ->
                                           match uu____14579 with
                                           | (x,uvs,e,c,gvs) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____14626 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____14626 in
                              let uu____14631 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                              (match uu____14631 with
                               | (lbs5,e22) ->
                                   ((let uu____14651 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1 in
                                     FStar_All.pipe_right uu____14651
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____14652 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     (uu____14652, cres,
                                       FStar_TypeChecker_Rel.trivial_guard))))))))
      | uu____14665 -> failwith "Impossible"
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
          let uu____14697 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____14697 with
           | (lbs1,e21) ->
               let uu____14716 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____14716 with
                | (env0,topt) ->
                    let uu____14735 = build_let_rec_env false env0 lbs1 in
                    (match uu____14735 with
                     | (lbs2,rec_env) ->
                         let uu____14754 = check_let_recs rec_env lbs2 in
                         (match uu____14754 with
                          | (lbs3,g_lbs) ->
                              let uu____14773 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___312_14796 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___312_14796.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___312_14796.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___313_14798 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___313_14798.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___313_14798.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___313_14798.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___313_14798.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____14773 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____14825 = tc_term env2 e21 in
                                   (match uu____14825 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____14842 =
                                            let uu____14843 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____14843 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____14842 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___314_14847 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___314_14847.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___314_14847.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___314_14847.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____14848 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____14848 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____14884 ->
                                                  (e, cres2, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  let cres3 =
                                                    let uu___315_14889 =
                                                      cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___315_14889.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___315_14889.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___315_14889.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____14892 -> failwith "Impossible"
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
          let uu____14921 = FStar_Options.ml_ish () in
          if uu____14921
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp in
             let uu____14924 =
               let uu____14929 =
                 let uu____14930 = FStar_Syntax_Subst.compress t in
                 uu____14930.FStar_Syntax_Syntax.n in
               let uu____14933 =
                 let uu____14934 = FStar_Syntax_Subst.compress lbdef in
                 uu____14934.FStar_Syntax_Syntax.n in
               (uu____14929, uu____14933) in
             match uu____14924 with
             | (FStar_Syntax_Syntax.Tm_arrow
                (formals,c),FStar_Syntax_Syntax.Tm_abs
                (actuals,uu____14940,uu____14941)) ->
                 let actuals1 =
                   let uu____14979 =
                     FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                   FStar_TypeChecker_Util.maybe_add_implicit_binders
                     uu____14979 actuals in
                 (if
                    (FStar_List.length formals) <>
                      (FStar_List.length actuals1)
                  then
                    (let actuals_msg =
                       let n1 = FStar_List.length actuals1 in
                       if n1 = (Prims.parse_int "1")
                       then "1 argument was found"
                       else
                         (let uu____15000 = FStar_Util.string_of_int n1 in
                          FStar_Util.format1 "%s arguments were found"
                            uu____15000) in
                     let formals_msg =
                       let n1 = FStar_List.length formals in
                       if n1 = (Prims.parse_int "1")
                       then "1 argument"
                       else
                         (let uu____15018 = FStar_Util.string_of_int n1 in
                          FStar_Util.format1 "%s arguments" uu____15018) in
                     let msg =
                       let uu____15026 =
                         FStar_Syntax_Print.term_to_string lbtyp in
                       let uu____15027 =
                         FStar_Syntax_Print.lbname_to_string lbname in
                       FStar_Util.format4
                         "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                         uu____15026 uu____15027 formals_msg actuals_msg in
                     FStar_Util.print1 "%s\n" msg)
                  else ();
                  (let quals =
                     FStar_TypeChecker_Env.lookup_effect_quals env
                       (FStar_Syntax_Util.comp_effect_name c) in
                   FStar_All.pipe_right quals
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
             | uu____15034 ->
                 let uu____15039 =
                   let uu____15040 =
                     let uu____15045 =
                       let uu____15046 =
                         FStar_Syntax_Print.term_to_string lbdef in
                       let uu____15047 =
                         FStar_Syntax_Print.term_to_string lbtyp in
                       FStar_Util.format2
                         "Only function literals with arrow types can be defined recursively; got %s : %s"
                         uu____15046 uu____15047 in
                     (uu____15045, (lbtyp.FStar_Syntax_Syntax.pos)) in
                   FStar_Errors.Error uu____15040 in
                 FStar_Exn.raise uu____15039) in
        let uu____15048 =
          FStar_List.fold_left
            (fun uu____15074  ->
               fun lb  ->
                 match uu____15074 with
                 | (lbs1,env1) ->
                     let uu____15094 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____15094 with
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
                              (let uu____15114 =
                                 let uu____15121 =
                                   let uu____15122 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____15122 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___316_15133 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___316_15133.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___316_15133.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___316_15133.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___316_15133.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___316_15133.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___316_15133.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___316_15133.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___316_15133.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___316_15133.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___316_15133.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___316_15133.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___316_15133.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___316_15133.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___316_15133.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___316_15133.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___316_15133.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___316_15133.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___316_15133.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___316_15133.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___316_15133.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___316_15133.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___316_15133.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___316_15133.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___316_15133.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___316_15133.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___316_15133.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___316_15133.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___316_15133.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___316_15133.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___316_15133.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___316_15133.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___316_15133.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___316_15133.FStar_TypeChecker_Env.dep_graph)
                                    }) t uu____15121 in
                               match uu____15114 with
                               | (t1,uu____15135,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____15139 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____15139);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____15141 =
                              termination_check_enabled
                                lb.FStar_Syntax_Syntax.lbname e t1 in
                            if uu____15141
                            then
                              let uu___317_15142 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___317_15142.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___317_15142.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___317_15142.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___317_15142.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___317_15142.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___317_15142.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___317_15142.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___317_15142.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___317_15142.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___317_15142.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___317_15142.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___317_15142.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1,
                                     univ_vars1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___317_15142.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___317_15142.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___317_15142.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___317_15142.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___317_15142.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___317_15142.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___317_15142.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___317_15142.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___317_15142.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___317_15142.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___317_15142.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___317_15142.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___317_15142.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___317_15142.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___317_15142.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___317_15142.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___317_15142.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___317_15142.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___317_15142.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___317_15142.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.dep_graph =
                                  (uu___317_15142.FStar_TypeChecker_Env.dep_graph)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname
                                (univ_vars1, t1) in
                          let lb1 =
                            let uu___318_15159 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___318_15159.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___318_15159.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____15048 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lbs  ->
      let uu____15182 =
        let uu____15191 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____15220 =
                     let uu____15221 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____15221.FStar_Syntax_Syntax.n in
                   match uu____15220 with
                   | FStar_Syntax_Syntax.Tm_abs uu____15224 -> ()
                   | uu____15241 ->
                       let uu____15242 =
                         let uu____15243 =
                           let uu____15248 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____15248) in
                         FStar_Errors.Error uu____15243 in
                       FStar_Exn.raise uu____15242);
                  (let uu____15249 =
                     let uu____15256 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____15256
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____15249 with
                   | (e,c,g) ->
                       ((let uu____15265 =
                           let uu____15266 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____15266 in
                         if uu____15265
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
        FStar_All.pipe_right uu____15191 FStar_List.unzip in
      match uu____15182 with
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
        let uu____15315 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____15315 with
        | (env1,uu____15333) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____15341 = check_lbtyp top_level env lb in
            (match uu____15341 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Exn.raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____15385 =
                     tc_maybe_toplevel_term
                       (let uu___319_15394 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___319_15394.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___319_15394.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___319_15394.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___319_15394.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___319_15394.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___319_15394.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___319_15394.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___319_15394.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___319_15394.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___319_15394.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___319_15394.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___319_15394.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___319_15394.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___319_15394.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___319_15394.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___319_15394.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___319_15394.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___319_15394.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___319_15394.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.failhard =
                            (uu___319_15394.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___319_15394.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___319_15394.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___319_15394.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___319_15394.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___319_15394.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___319_15394.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___319_15394.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___319_15394.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___319_15394.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___319_15394.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___319_15394.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___319_15394.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___319_15394.FStar_TypeChecker_Env.dep_graph)
                        }) e11 in
                   match uu____15385 with
                   | (e12,c1,g1) ->
                       let uu____15408 =
                         let uu____15413 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____15417  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____15413 e12 c1 wf_annot in
                       (match uu____15408 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____15432 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____15432
                              then
                                let uu____15433 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____15434 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____15435 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____15433 uu____15434 uu____15435
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
            let uu____15469 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____15469 with
             | (univ_opening,univ_vars1) ->
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                   univ_opening, env))
        | uu____15508 ->
            let uu____15509 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____15509 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____15558 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____15558)
                 else
                   (let uu____15566 = FStar_Syntax_Util.type_u () in
                    match uu____15566 with
                    | (k,uu____15586) ->
                        let uu____15587 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____15587 with
                         | (t2,uu____15609,g) ->
                             ((let uu____15612 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____15612
                               then
                                 let uu____15613 =
                                   let uu____15614 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____15614 in
                                 let uu____15615 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____15613 uu____15615
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____15618 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____15618))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun uu____15626  ->
      match uu____15626 with
      | (x,imp) ->
          let uu____15645 = FStar_Syntax_Util.type_u () in
          (match uu____15645 with
           | (tu,u) ->
               ((let uu____15665 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____15665
                 then
                   let uu____15666 = FStar_Syntax_Print.bv_to_string x in
                   let uu____15667 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____15668 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____15666 uu____15667 uu____15668
                 else ());
                (let uu____15670 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____15670 with
                 | (t,uu____15690,g) ->
                     let x1 =
                       ((let uu___320_15698 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___320_15698.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___320_15698.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____15700 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____15700
                       then
                         let uu____15701 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1) in
                         let uu____15702 =
                           FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____15701 uu____15702
                       else ());
                      (let uu____15704 = push_binding env x1 in
                       (x1, uu____15704, g, u))))))
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
            let uu____15794 = tc_binder env1 b in
            (match uu____15794 with
             | (b1,env',g,u) ->
                 let uu____15835 = aux env' bs2 in
                 (match uu____15835 with
                  | (bs3,env'1,g',us) ->
                      let uu____15888 =
                        let uu____15889 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____15889 in
                      ((b1 :: bs3), env'1, uu____15888, (u :: us)))) in
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
          (fun uu____15974  ->
             fun uu____15975  ->
               match (uu____15974, uu____15975) with
               | ((t,imp),(args1,g)) ->
                   let uu____16044 = tc_term env1 t in
                   (match uu____16044 with
                    | (t1,uu____16062,g') ->
                        let uu____16064 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____16064))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____16106  ->
             match uu____16106 with
             | (pats1,g) ->
                 let uu____16131 = tc_args env p in
                 (match uu____16131 with
                  | (args,g') ->
                      let uu____16144 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____16144))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let uu____16157 = tc_maybe_toplevel_term env e in
      match uu____16157 with
      | (e1,c,g) ->
          let uu____16173 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____16173
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____16186 =
               let uu____16191 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____16191
               then
                 let uu____16196 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____16196, false)
               else
                 (let uu____16198 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____16198, true)) in
             match uu____16186 with
             | (target_comp,allow_ghost) ->
                 let uu____16207 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____16207 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____16217 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____16217)
                  | uu____16218 ->
                      if allow_ghost
                      then
                        let uu____16227 =
                          let uu____16228 =
                            let uu____16233 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____16233, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____16228 in
                        FStar_Exn.raise uu____16227
                      else
                        (let uu____16241 =
                           let uu____16242 =
                             let uu____16247 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____16247, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____16242 in
                         FStar_Exn.raise uu____16241)))
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
      let uu____16266 = tc_tot_or_gtot_term env t in
      match uu____16266 with
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
      (let uu____16294 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____16294
       then
         let uu____16295 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____16295
       else ());
      (let env1 =
         let uu___321_16298 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___321_16298.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___321_16298.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___321_16298.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___321_16298.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___321_16298.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___321_16298.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___321_16298.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___321_16298.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___321_16298.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___321_16298.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___321_16298.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___321_16298.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___321_16298.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___321_16298.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___321_16298.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___321_16298.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___321_16298.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___321_16298.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___321_16298.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___321_16298.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.tc_term =
             (uu___321_16298.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___321_16298.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___321_16298.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___321_16298.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___321_16298.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___321_16298.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___321_16298.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___321_16298.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___321_16298.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___321_16298.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___321_16298.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.dep_graph =
             (uu___321_16298.FStar_TypeChecker_Env.dep_graph)
         } in
       let uu____16305 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____16338) ->
             let uu____16339 =
               let uu____16340 =
                 let uu____16345 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____16345) in
               FStar_Errors.Error uu____16340 in
             FStar_Exn.raise uu____16339 in
       match uu____16305 with
       | (t,c,g) ->
           let uu____16361 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____16361
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____16371 =
                let uu____16372 =
                  let uu____16377 =
                    let uu____16378 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____16378 in
                  let uu____16379 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____16377, uu____16379) in
                FStar_Errors.Error uu____16372 in
              FStar_Exn.raise uu____16371))
let level_of_type_fail:
  'Auu____16390 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____16390
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____16403 =
          let uu____16404 =
            let uu____16409 =
              let uu____16410 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format2
                "Expected a term of type 'Type'; got %s : %s" uu____16410 t in
            let uu____16411 = FStar_TypeChecker_Env.get_range env in
            (uu____16409, uu____16411) in
          FStar_Errors.Error uu____16404 in
        FStar_Exn.raise uu____16403
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____16428 =
            let uu____16429 = FStar_Syntax_Util.unrefine t1 in
            uu____16429.FStar_Syntax_Syntax.n in
          match uu____16428 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____16433 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____16436 = FStar_Syntax_Util.type_u () in
                 match uu____16436 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___324_16444 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___324_16444.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___324_16444.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___324_16444.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___324_16444.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___324_16444.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___324_16444.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___324_16444.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___324_16444.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___324_16444.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___324_16444.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___324_16444.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___324_16444.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___324_16444.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___324_16444.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___324_16444.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___324_16444.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___324_16444.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___324_16444.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___324_16444.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___324_16444.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___324_16444.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___324_16444.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___324_16444.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___324_16444.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___324_16444.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___324_16444.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___324_16444.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___324_16444.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___324_16444.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___324_16444.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___324_16444.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___324_16444.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___324_16444.FStar_TypeChecker_Env.dep_graph)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____16448 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____16448
                       | uu____16449 ->
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
      let uu____16458 =
        let uu____16459 = FStar_Syntax_Subst.compress e in
        uu____16459.FStar_Syntax_Syntax.n in
      match uu____16458 with
      | FStar_Syntax_Syntax.Tm_bvar uu____16464 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____16469 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____16496 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____16512) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____16535,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____16562) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____16569 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____16569 with | ((uu____16580,t),uu____16582) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16587,(FStar_Util.Inl t,uu____16589),uu____16590) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16637,(FStar_Util.Inr c,uu____16639),uu____16640) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____16690;
             FStar_Syntax_Syntax.vars = uu____16691;_},us)
          ->
          let uu____16697 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____16697 with
           | ((us',t),uu____16710) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____16716 =
                     let uu____16717 =
                       let uu____16722 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____16722) in
                     FStar_Errors.Error uu____16717 in
                   FStar_Exn.raise uu____16716)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____16738 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____16739 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____16749) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____16772 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____16772 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____16792  ->
                      match uu____16792 with
                      | (b,uu____16798) ->
                          let uu____16799 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____16799) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____16804 = universe_of_aux env res in
                 level_of_type env res uu____16804 in
               let u_c =
                 let uu____16806 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____16806 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____16810 = universe_of_aux env trepr in
                     level_of_type env trepr uu____16810 in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____16903 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____16918 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____16957 ->
                let uu____16958 = universe_of_aux env hd3 in
                (uu____16958, args1)
            | FStar_Syntax_Syntax.Tm_name uu____16971 ->
                let uu____16972 = universe_of_aux env hd3 in
                (uu____16972, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____16985 ->
                let uu____17002 = universe_of_aux env hd3 in
                (uu____17002, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____17015 ->
                let uu____17022 = universe_of_aux env hd3 in
                (uu____17022, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____17035 ->
                let uu____17062 = universe_of_aux env hd3 in
                (uu____17062, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____17075 ->
                let uu____17082 = universe_of_aux env hd3 in
                (uu____17082, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____17095 ->
                let uu____17096 = universe_of_aux env hd3 in
                (uu____17096, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____17109 ->
                let uu____17122 = universe_of_aux env hd3 in
                (uu____17122, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____17135 ->
                let uu____17142 = universe_of_aux env hd3 in
                (uu____17142, args1)
            | FStar_Syntax_Syntax.Tm_type uu____17155 ->
                let uu____17156 = universe_of_aux env hd3 in
                (uu____17156, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____17169,hd4::uu____17171) ->
                let uu____17236 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____17236 with
                 | (uu____17251,uu____17252,hd5) ->
                     let uu____17270 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____17270 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____17321 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____17323 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____17323 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____17374 ->
                let uu____17375 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____17375 with
                 | (env1,uu____17397) ->
                     let env2 =
                       let uu___325_17403 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___325_17403.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___325_17403.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___325_17403.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___325_17403.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___325_17403.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___325_17403.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___325_17403.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___325_17403.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___325_17403.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___325_17403.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___325_17403.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___325_17403.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___325_17403.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___325_17403.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___325_17403.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___325_17403.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___325_17403.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___325_17403.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___325_17403.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___325_17403.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___325_17403.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___325_17403.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___325_17403.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___325_17403.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___325_17403.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___325_17403.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___325_17403.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___325_17403.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___325_17403.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___325_17403.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.dep_graph =
                           (uu___325_17403.FStar_TypeChecker_Env.dep_graph)
                       } in
                     ((let uu____17405 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____17405
                       then
                         let uu____17406 =
                           let uu____17407 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____17407 in
                         let uu____17408 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____17406 uu____17408
                       else ());
                      (let uu____17410 = tc_term env2 hd3 in
                       match uu____17410 with
                       | (uu____17431,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____17432;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____17434;
                                        FStar_Syntax_Syntax.comp =
                                          uu____17435;_},g)
                           ->
                           ((let uu____17446 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____17446
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____17457 = type_of_head true hd1 args in
          (match uu____17457 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____17497 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____17497 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____17541 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____17541)))
      | FStar_Syntax_Syntax.Tm_match (uu____17544,hd1::uu____17546) ->
          let uu____17611 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____17611 with
           | (uu____17614,uu____17615,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____17633,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____17676 = universe_of_aux env e in
      level_of_type env e uu____17676
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tps  ->
      let uu____17695 = tc_binders env tps in
      match uu____17695 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))