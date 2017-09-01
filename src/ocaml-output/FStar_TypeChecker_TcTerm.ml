open Prims
let instantiate_both: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___93_5 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___93_5.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___93_5.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___93_5.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___93_5.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___93_5.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___93_5.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___93_5.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___93_5.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___93_5.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___93_5.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___93_5.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___93_5.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___93_5.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___93_5.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___93_5.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___93_5.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___93_5.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___93_5.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___93_5.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___93_5.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.type_of =
        (uu___93_5.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___93_5.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___93_5.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___93_5.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___93_5.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___93_5.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___93_5.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___93_5.FStar_TypeChecker_Env.identifier_info)
    }
let no_inst: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___94_10 = env in
    {
      FStar_TypeChecker_Env.solver =
        (uu___94_10.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___94_10.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___94_10.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___94_10.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___94_10.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___94_10.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___94_10.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___94_10.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___94_10.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___94_10.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___94_10.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___94_10.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___94_10.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___94_10.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___94_10.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___94_10.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___94_10.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___94_10.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___94_10.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.failhard =
        (uu___94_10.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.type_of =
        (uu___94_10.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___94_10.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___94_10.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___94_10.FStar_TypeChecker_Env.qname_and_index);
      FStar_TypeChecker_Env.proof_ns =
        (uu___94_10.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth = (uu___94_10.FStar_TypeChecker_Env.synth);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___94_10.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___94_10.FStar_TypeChecker_Env.identifier_info)
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
  fun uu___88_57  ->
    match uu___88_57 with
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
      let uu___95_226 = lc in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___95_226.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___95_226.FStar_Syntax_Syntax.cflags);
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
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____310 -> false
                   | uu____311 -> true)
                else false
            | uu____313 -> true in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____316 =
                  let uu____319 =
                    (let uu____322 = should_return t in
                     Prims.op_Negation uu____322) ||
                      (let uu____324 =
                         FStar_TypeChecker_Env.should_verify env in
                       Prims.op_Negation uu____324) in
                  if uu____319
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e in
                FStar_Syntax_Util.lcomp_of_comp uu____316
            | FStar_Util.Inr lc -> lc in
          let t = lc.FStar_Syntax_Syntax.res_typ in
          let uu____332 =
            let uu____339 = FStar_TypeChecker_Env.expected_typ env in
            match uu____339 with
            | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                ((let uu____350 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High in
                  if uu____350
                  then
                    let uu____351 = FStar_Syntax_Print.term_to_string t in
                    let uu____352 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____351
                      uu____352
                  else ());
                 (let uu____354 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t' in
                  match uu____354 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____370 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____370 with
                       | (e2,g) ->
                           ((let uu____384 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____384
                             then
                               let uu____385 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____386 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____387 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____388 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____385 uu____386 uu____387 uu____388
                             else ());
                            (let msg =
                               let uu____395 =
                                 FStar_TypeChecker_Rel.is_trivial g in
                               if uu____395
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_40  ->
                                      FStar_Pervasives_Native.Some _0_40)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             let uu____412 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1 in
                             match uu____412 with
                             | (lc2,g2) ->
                                 ((memo_tk e2 t'), (set_lcomp_result lc2 t'),
                                   g2)))))) in
          match uu____332 with
          | (e1,lc1,g) ->
              ((let uu____435 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low in
                if uu____435
                then
                  let uu____436 = FStar_Syntax_Print.lcomp_to_string lc1 in
                  FStar_Util.print1 "Return comp type is %s\n" uu____436
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
        let uu____462 = FStar_TypeChecker_Env.expected_typ env in
        match uu____462 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____472 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____472 with
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
      fun uu____508  ->
        match uu____508 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____537 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____537
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____539 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____539
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____541 =
              match copt with
              | FStar_Pervasives_Native.Some uu____554 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____557 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____559 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____559)) in
                  if uu____557
                  then
                    let uu____566 =
                      let uu____569 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos in
                      FStar_Pervasives_Native.Some uu____569 in
                    (uu____566, c)
                  else
                    (let uu____573 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____573
                     then
                       let uu____580 = tot_or_gtot c in
                       (FStar_Pervasives_Native.None, uu____580)
                     else
                       (let uu____584 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____584
                        then
                          let uu____591 =
                            let uu____594 = tot_or_gtot c in
                            FStar_Pervasives_Native.Some uu____594 in
                          (uu____591, c)
                        else (FStar_Pervasives_Native.None, c))) in
            (match uu____541 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let uu____620 =
                        FStar_TypeChecker_Util.check_comp env e c2 expected_c in
                      (match uu____620 with
                       | (e1,uu____634,g) ->
                           let g1 =
                             let uu____637 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_TypeChecker_Util.label_guard uu____637
                               "could not prove post-condition" g in
                           ((let uu____639 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low in
                             if uu____639
                             then
                               let uu____640 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos in
                               let uu____641 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1 in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____640 uu____641
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c2)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c2) in
                             (e2, expected_c, g1))))))
let no_logical_guard:
  'Auu____652 'Auu____653 .
    FStar_TypeChecker_Env.env ->
      ('Auu____653,'Auu____652,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 ->
        ('Auu____653,'Auu____652,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uu____673  ->
      match uu____673 with
      | (te,kt,f) ->
          let uu____683 = FStar_TypeChecker_Rel.guard_form f in
          (match uu____683 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____691 =
                 let uu____692 =
                   let uu____697 =
                     FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                       env f1 in
                   let uu____698 = FStar_TypeChecker_Env.get_range env in
                   (uu____697, uu____698) in
                 FStar_Errors.Error uu____692 in
               FStar_Exn.raise uu____691)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____709 = FStar_TypeChecker_Env.expected_typ env in
    match uu____709 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None"
    | FStar_Pervasives_Native.Some t ->
        let uu____713 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____713
let check_smt_pat:
  'Auu____724 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,'Auu____724) FStar_Pervasives_Native.tuple2
          Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____757 = FStar_Syntax_Util.is_smt_lemma t in
          if uu____757
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____758;
                  FStar_Syntax_Syntax.effect_name = uu____759;
                  FStar_Syntax_Syntax.result_typ = uu____760;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____764)::[];
                  FStar_Syntax_Syntax.flags = uu____765;_}
                ->
                let pat_vars =
                  let uu____813 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta] env pats in
                  FStar_Syntax_Free.names uu____813 in
                let uu____814 =
                  FStar_All.pipe_right bs
                    (FStar_Util.find_opt
                       (fun uu____841  ->
                          match uu____841 with
                          | (b,uu____847) ->
                              let uu____848 = FStar_Util.set_mem b pat_vars in
                              Prims.op_Negation uu____848)) in
                (match uu____814 with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some (x,uu____854) ->
                     let uu____859 =
                       let uu____860 = FStar_Syntax_Print.bv_to_string x in
                       FStar_Util.format1
                         "Pattern misses at least one bound variable: %s"
                         uu____860 in
                     FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____859)
            | uu____861 -> failwith "Impossible"
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
        match env.FStar_TypeChecker_Env.letrecs with
        | [] -> []
        | letrecs ->
            let r = FStar_TypeChecker_Env.get_range env in
            let env1 =
              let uu___96_908 = env in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___96_908.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___96_908.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___96_908.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___96_908.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___96_908.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___96_908.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___96_908.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___96_908.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___96_908.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___96_908.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___96_908.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___96_908.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___96_908.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___96_908.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___96_908.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___96_908.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___96_908.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___96_908.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___96_908.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.failhard =
                  (uu___96_908.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.type_of =
                  (uu___96_908.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___96_908.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___96_908.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qname_and_index =
                  (uu___96_908.FStar_TypeChecker_Env.qname_and_index);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___96_908.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth =
                  (uu___96_908.FStar_TypeChecker_Env.synth);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___96_908.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___96_908.FStar_TypeChecker_Env.identifier_info)
              } in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid in
            let decreases_clause bs c =
              let filter_types_and_functions bs1 =
                FStar_All.pipe_right bs1
                  (FStar_List.collect
                     (fun uu____942  ->
                        match uu____942 with
                        | (b,uu____950) ->
                            let t =
                              let uu____952 =
                                FStar_Syntax_Util.unrefine
                                  b.FStar_Syntax_Syntax.sort in
                              FStar_TypeChecker_Normalize.unfold_whnf env1
                                uu____952 in
                            (match t.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_type uu____955 -> []
                             | FStar_Syntax_Syntax.Tm_arrow uu____956 -> []
                             | uu____969 ->
                                 let uu____970 =
                                   FStar_Syntax_Syntax.bv_to_name b in
                                 [uu____970]))) in
              let as_lex_list dec =
                let uu____975 = FStar_Syntax_Util.head_and_args dec in
                match uu____975 with
                | (head1,uu____991) ->
                    (match head1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.lexcons_lid
                         -> dec
                     | uu____1013 -> mk_lex_list [dec]) in
              let cflags = FStar_Syntax_Util.comp_flags c in
              let uu____1017 =
                FStar_All.pipe_right cflags
                  (FStar_List.tryFind
                     (fun uu___89_1026  ->
                        match uu___89_1026 with
                        | FStar_Syntax_Syntax.DECREASES uu____1027 -> true
                        | uu____1030 -> false)) in
              match uu____1017 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                  dec) -> as_lex_list dec
              | uu____1034 ->
                  let xs = FStar_All.pipe_right bs filter_types_and_functions in
                  (match xs with | x::[] -> x | uu____1043 -> mk_lex_list xs) in
            let previous_dec = decreases_clause actuals expected_c in
            let guard_one_letrec uu____1060 =
              match uu____1060 with
              | (l,t) ->
                  let uu____1073 =
                    let uu____1074 = FStar_Syntax_Subst.compress t in
                    uu____1074.FStar_Syntax_Syntax.n in
                  (match uu____1073 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____1133  ->
                                 match uu____1133 with
                                 | (x,imp) ->
                                     let uu____1144 =
                                       FStar_Syntax_Syntax.is_null_bv x in
                                     if uu____1144
                                     then
                                       let uu____1149 =
                                         let uu____1150 =
                                           let uu____1153 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x in
                                           FStar_Pervasives_Native.Some
                                             uu____1153 in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____1150
                                           x.FStar_Syntax_Syntax.sort in
                                       (uu____1149, imp)
                                     else (x, imp))) in
                       let uu____1155 =
                         FStar_Syntax_Subst.open_comp formals1 c in
                       (match uu____1155 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1 in
                            let precedes1 =
                              let uu____1172 =
                                let uu____1173 =
                                  let uu____1174 =
                                    FStar_Syntax_Syntax.as_arg dec in
                                  let uu____1175 =
                                    let uu____1178 =
                                      FStar_Syntax_Syntax.as_arg previous_dec in
                                    [uu____1178] in
                                  uu____1174 :: uu____1175 in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____1173 in
                              uu____1172 FStar_Pervasives_Native.None r in
                            let uu____1181 = FStar_Util.prefix formals2 in
                            (match uu____1181 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___97_1226 = last1 in
                                   let uu____1227 =
                                     FStar_Syntax_Util.refine last1 precedes1 in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___97_1226.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___97_1226.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____1227
                                   } in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)] in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1 in
                                 ((let uu____1253 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low in
                                   if uu____1253
                                   then
                                     let uu____1254 =
                                       FStar_Syntax_Print.lbname_to_string l in
                                     let uu____1255 =
                                       FStar_Syntax_Print.term_to_string t in
                                     let uu____1256 =
                                       FStar_Syntax_Print.term_to_string t' in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____1254 uu____1255 uu____1256
                                   else ());
                                  (l, t'))))
                   | uu____1260 ->
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
        (let uu___98_1691 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___98_1691.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___98_1691.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___98_1691.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___98_1691.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___98_1691.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___98_1691.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___98_1691.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___98_1691.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___98_1691.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___98_1691.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___98_1691.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___98_1691.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___98_1691.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___98_1691.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___98_1691.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___98_1691.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___98_1691.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___98_1691.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___98_1691.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___98_1691.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.type_of =
             (uu___98_1691.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___98_1691.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___98_1691.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___98_1691.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___98_1691.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___98_1691.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___98_1691.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___98_1691.FStar_TypeChecker_Env.identifier_info)
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
      (let uu____1703 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1703
       then
         let uu____1704 =
           let uu____1705 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1705 in
         let uu____1706 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1704 uu____1706
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1715 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1746 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1753 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1770 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1771 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1772 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1773 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1774 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1791 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1804 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1811 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1817 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1817 with
            | (e2,c,g) ->
                let g1 =
                  let uu___99_1834 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___99_1834.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___99_1834.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___99_1834.FStar_TypeChecker_Env.implicits)
                  } in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1851 = FStar_Syntax_Util.type_u () in
           (match uu____1851 with
            | (t,u) ->
                let uu____1864 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1864 with
                 | (e2,c,g) ->
                     let uu____1880 =
                       let uu____1895 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____1895 with
                       | (env2,uu____1917) -> tc_pats env2 pats in
                     (match uu____1880 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___100_1951 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___100_1951.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___100_1951.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___100_1951.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____1952 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos in
                          let uu____1955 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____1952, c, uu____1955))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1963 =
             let uu____1964 = FStar_Syntax_Subst.compress e1 in
             uu____1964.FStar_Syntax_Syntax.n in
           (match uu____1963 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1973,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1975;
                               FStar_Syntax_Syntax.lbtyp = uu____1976;
                               FStar_Syntax_Syntax.lbeff = uu____1977;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____2002 =
                  let uu____2009 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit in
                  tc_term uu____2009 e11 in
                (match uu____2002 with
                 | (e12,c1,g1) ->
                     let uu____2019 = tc_term env1 e2 in
                     (match uu____2019 with
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
                            let uu____2043 =
                              let uu____2046 =
                                let uu____2047 =
                                  let uu____2060 =
                                    let uu____2067 =
                                      let uu____2070 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13) in
                                      [uu____2070] in
                                    (false, uu____2067) in
                                  (uu____2060, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____2047 in
                              FStar_Syntax_Syntax.mk uu____2046 in
                            uu____2043 FStar_Pervasives_Native.None
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
                          let uu____2092 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____2092)))
            | uu____2095 ->
                let uu____2096 = tc_term env1 e1 in
                (match uu____2096 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____2118) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____2135 = tc_term env1 e1 in
           (match uu____2135 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____2159) ->
           let uu____2206 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2206 with
            | (env0,uu____2220) ->
                let uu____2225 = tc_comp env0 expected_c in
                (match uu____2225 with
                 | (expected_c1,uu____2239,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____2244 =
                       let uu____2251 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____2251 e1 in
                     (match uu____2244 with
                      | (e2,c',g') ->
                          let uu____2261 =
                            let uu____2268 =
                              let uu____2273 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____2273) in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____2268 in
                          (match uu____2261 with
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
                                 let uu____2328 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____2328 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (fun f1  ->
                                          let uu____2337 =
                                            FStar_Syntax_Util.mk_squash f1 in
                                          FStar_TypeChecker_Common.mk_by_tactic
                                            tactic uu____2337) in
                               let uu____2338 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____2338 with
                                | (e5,c,f2) ->
                                    let uu____2354 =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, uu____2354))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____2358) ->
           let uu____2405 = FStar_Syntax_Util.type_u () in
           (match uu____2405 with
            | (k,u) ->
                let uu____2418 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____2418 with
                 | (t1,uu____2432,f) ->
                     let uu____2434 =
                       let uu____2441 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____2441 e1 in
                     (match uu____2434 with
                      | (e2,c,g) ->
                          let uu____2451 =
                            let uu____2456 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____2460  ->
                                    FStar_Util.return_all
                                      FStar_TypeChecker_Err.ill_kinded_type))
                              uu____2456 e2 c f in
                          (match uu____2451 with
                           | (c1,f1) ->
                               let uu____2469 =
                                 let uu____2476 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_ascribed
                                        (e2,
                                          ((FStar_Util.Inl t1),
                                            FStar_Pervasives_Native.None),
                                          (FStar_Pervasives_Native.Some
                                             (c1.FStar_Syntax_Syntax.eff_name))))
                                     FStar_Pervasives_Native.None
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____2476 c1 in
                               (match uu____2469 with
                                | (e3,c2,f2) ->
                                    let uu____2516 =
                                      let uu____2517 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____2517 in
                                    (e3, c2, uu____2516))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____2518;
              FStar_Syntax_Syntax.vars = uu____2519;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2582 = FStar_Syntax_Util.head_and_args top in
           (match uu____2582 with
            | (unary_op,uu____2604) ->
                let head1 =
                  let uu____2628 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2628 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____2666);
              FStar_Syntax_Syntax.pos = uu____2667;
              FStar_Syntax_Syntax.vars = uu____2668;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2731 = FStar_Syntax_Util.head_and_args top in
           (match uu____2731 with
            | (unary_op,uu____2753) ->
                let head1 =
                  let uu____2777 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2777 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____2815;
              FStar_Syntax_Syntax.vars = uu____2816;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____2849 =
               let uu____2856 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____2856 with | (env0,uu____2870) -> tc_term env0 e1 in
             match uu____2849 with
             | (e2,c,g) ->
                 let uu____2884 = FStar_Syntax_Util.head_and_args top in
                 (match uu____2884 with
                  | (reify_op,uu____2906) ->
                      let u_c =
                        let uu____2928 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____2928 with
                        | (uu____2935,c',uu____2937) ->
                            let uu____2938 =
                              let uu____2939 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____2939.FStar_Syntax_Syntax.n in
                            (match uu____2938 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____2943 ->
                                 let uu____2944 = FStar_Syntax_Util.type_u () in
                                 (match uu____2944 with
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
                                            let uu____2956 =
                                              let uu____2957 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____2958 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____2959 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____2957 uu____2958
                                                uu____2959 in
                                            failwith uu____2956);
                                       u))) in
                      let repr =
                        let uu____2961 = c.FStar_Syntax_Syntax.comp () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____2961 u_c in
                      let e3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (reify_op, [(e2, aqual)]))
                          FStar_Pervasives_Native.None
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____2982 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____2982
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____2983 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____2983 with
                       | (e4,c2,g') ->
                           let uu____2999 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____2999)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____3001;
              FStar_Syntax_Syntax.vars = uu____3002;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____3044 =
               let uu____3045 =
                 let uu____3046 =
                   let uu____3051 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____3051, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____3046 in
               FStar_Exn.raise uu____3045 in
             let uu____3058 = FStar_Syntax_Util.head_and_args top in
             match uu____3058 with
             | (reflect_op,uu____3080) ->
                 let uu____3101 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____3101 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____3134 =
                        let uu____3135 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____3135 in
                      if uu____3134
                      then no_reflect ()
                      else
                        (let uu____3145 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____3145 with
                         | (env_no_ex,topt) ->
                             let uu____3164 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____3184 =
                                   let uu____3187 =
                                     let uu____3188 =
                                       let uu____3203 =
                                         let uu____3206 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____3207 =
                                           let uu____3210 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____3210] in
                                         uu____3206 :: uu____3207 in
                                       (repr, uu____3203) in
                                     FStar_Syntax_Syntax.Tm_app uu____3188 in
                                   FStar_Syntax_Syntax.mk uu____3187 in
                                 uu____3184 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos in
                               let uu____3216 =
                                 let uu____3223 =
                                   let uu____3224 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____3224
                                     FStar_Pervasives_Native.fst in
                                 tc_tot_or_gtot_term uu____3223 t in
                               match uu____3216 with
                               | (t1,uu____3252,g) ->
                                   let uu____3254 =
                                     let uu____3255 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____3255.FStar_Syntax_Syntax.n in
                                   (match uu____3254 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____3270,(res,uu____3272)::
                                         (wp,uu____3274)::[])
                                        -> (t1, res, wp, g)
                                    | uu____3317 -> failwith "Impossible") in
                             (match uu____3164 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____3348 =
                                    let uu____3353 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____3353 with
                                    | (e2,c,g) ->
                                        ((let uu____3368 =
                                            let uu____3369 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____3369 in
                                          if uu____3368
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____3379 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____3379 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____3387 =
                                                  let uu____3394 =
                                                    let uu____3399 =
                                                      let uu____3400 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____3401 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____3400 uu____3401 in
                                                    (uu____3399,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____3394] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____3387);
                                               (let uu____3410 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____3410)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____3412 =
                                                let uu____3413 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____3413 in
                                              (e2, uu____3412))) in
                                  (match uu____3348 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____3423 =
                                           let uu____3424 =
                                             let uu____3425 =
                                               let uu____3426 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____3426] in
                                             let uu____3427 =
                                               let uu____3436 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____3436] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____3425;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____3427;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____3424 in
                                         FStar_All.pipe_right uu____3423
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           FStar_Pervasives_Native.None
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____3456 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____3456 with
                                        | (e4,c1,g') ->
                                            let uu____3472 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____3472))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____3519 =
               let uu____3520 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____3520 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____3519 instantiate_both in
           ((let uu____3536 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____3536
             then
               let uu____3537 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____3538 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____3537
                 uu____3538
             else ());
            (let isquote =
               match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.quote_lid
                   -> true
               | uu____3542 -> false in
             let uu____3543 = tc_term (no_inst env2) head1 in
             match uu____3543 with
             | (head2,chead,g_head) ->
                 let uu____3559 =
                   let uu____3566 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____3566
                   then
                     let uu____3573 =
                       let uu____3580 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____3580 in
                     match uu____3573 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____3593 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____3595 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c in
                                 Prims.op_Negation uu____3595))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                           if uu____3593
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c in
                         (e1, c1, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2 in
                      let uu____3600 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env3 head2 chead g_head args
                        uu____3600) in
                 (match uu____3559 with
                  | (e1,c,g) ->
                      ((let uu____3613 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____3613
                        then
                          let uu____3614 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____3614
                        else ());
                       (let uu____3616 = comp_check_expected_typ env0 e1 c in
                        match uu____3616 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____3633 =
                                let uu____3634 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____3634.FStar_Syntax_Syntax.n in
                              match uu____3633 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____3638) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___101_3700 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___101_3700.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___101_3700.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___101_3700.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____3749 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____3751 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____3751 in
                            ((let uu____3753 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____3753
                              then
                                let uu____3754 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____3755 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____3754 uu____3755
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____3795 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____3795 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____3815 = tc_term env12 e1 in
                (match uu____3815 with
                 | (e11,c1,g1) ->
                     let uu____3831 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____3841 = FStar_Syntax_Util.type_u () in
                           (match uu____3841 with
                            | (k,uu____3851) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____3853 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____3853, res_t)) in
                     (match uu____3831 with
                      | (env_branches,res_t) ->
                          ((let uu____3863 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____3863
                            then
                              let uu____3864 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____3864
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____3950 =
                              let uu____3955 =
                                FStar_List.fold_right
                                  (fun uu____4001  ->
                                     fun uu____4002  ->
                                       match (uu____4001, uu____4002) with
                                       | ((uu____4065,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____4125 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____4125))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____3955 with
                              | (cases,g) ->
                                  let uu____4164 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____4164, g) in
                            match uu____3950 with
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
                                           (fun uu____4260  ->
                                              match uu____4260 with
                                              | ((pat,wopt,br),uu____4288,lc,uu____4290)
                                                  ->
                                                  let uu____4303 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____4303))) in
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
                                  let uu____4358 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____4358
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____4365 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____4365 in
                                     let lb =
                                       let uu____4369 =
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
                                           uu____4369;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____4373 =
                                         let uu____4376 =
                                           let uu____4377 =
                                             let uu____4390 =
                                               let uu____4391 =
                                                 let uu____4392 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____4392] in
                                               FStar_Syntax_Subst.close
                                                 uu____4391 e_match in
                                             ((false, [lb]), uu____4390) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____4377 in
                                         FStar_Syntax_Syntax.mk uu____4376 in
                                       uu____4373
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____4405 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____4405
                                  then
                                    let uu____4406 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____4407 =
                                      let uu____4408 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____4408 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____4406 uu____4407
                                  else ());
                                 (let uu____4410 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____4410))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____4413;
                FStar_Syntax_Syntax.lbunivs = uu____4414;
                FStar_Syntax_Syntax.lbtyp = uu____4415;
                FStar_Syntax_Syntax.lbeff = uu____4416;
                FStar_Syntax_Syntax.lbdef = uu____4417;_}::[]),uu____4418)
           ->
           ((let uu____4438 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____4438
             then
               let uu____4439 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____4439
             else ());
            (let uu____4441 =
               FStar_TypeChecker_Env.debug env1
                 (FStar_Options.Other "2-Phase-Checking") in
             if uu____4441
             then
               let uu____4448 =
                 check_top_level_let
                   (let uu___102_4457 = env1 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___102_4457.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___102_4457.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___102_4457.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___102_4457.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___102_4457.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___102_4457.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___102_4457.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___102_4457.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___102_4457.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___102_4457.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___102_4457.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___102_4457.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___102_4457.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___102_4457.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___102_4457.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___102_4457.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___102_4457.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___102_4457.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___102_4457.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___102_4457.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.type_of =
                        (uu___102_4457.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___102_4457.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___102_4457.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___102_4457.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___102_4457.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___102_4457.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___102_4457.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___102_4457.FStar_TypeChecker_Env.identifier_info)
                    }) top in
               match uu____4448 with
               | (lax_top,l,g) ->
                   ((let uu____4468 =
                       FStar_Syntax_Print.term_to_string lax_top in
                     FStar_Util.print1 "Phase 1: checked %s\n" uu____4468);
                    (let uu____4469 =
                       FStar_TypeChecker_Env.should_verify env1 in
                     if uu____4469
                     then check_top_level_let env1 lax_top
                     else (lax_top, l, g)))
             else check_top_level_let env1 top))
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____4478),uu____4479) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____4494;
                FStar_Syntax_Syntax.lbunivs = uu____4495;
                FStar_Syntax_Syntax.lbtyp = uu____4496;
                FStar_Syntax_Syntax.lbeff = uu____4497;
                FStar_Syntax_Syntax.lbdef = uu____4498;_}::uu____4499),uu____4500)
           ->
           ((let uu____4522 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____4522
             then
               let uu____4523 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____4523
             else ());
            (let uu____4525 =
               FStar_TypeChecker_Env.debug env1
                 (FStar_Options.Other "2-Phase-Checking") in
             if uu____4525
             then
               let uu____4532 =
                 check_top_level_let_rec
                   (let uu___103_4541 = env1 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___103_4541.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___103_4541.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___103_4541.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___103_4541.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___103_4541.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___103_4541.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___103_4541.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___103_4541.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___103_4541.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___103_4541.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___103_4541.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___103_4541.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___103_4541.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___103_4541.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___103_4541.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___103_4541.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___103_4541.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___103_4541.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___103_4541.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.failhard =
                        (uu___103_4541.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.type_of =
                        (uu___103_4541.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___103_4541.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___103_4541.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qname_and_index =
                        (uu___103_4541.FStar_TypeChecker_Env.qname_and_index);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___103_4541.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth =
                        (uu___103_4541.FStar_TypeChecker_Env.synth);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___103_4541.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___103_4541.FStar_TypeChecker_Env.identifier_info)
                    }) top in
               match uu____4532 with
               | (lax_top,l,g) ->
                   ((let uu____4552 =
                       FStar_Syntax_Print.term_to_string lax_top in
                     FStar_Util.print1 "Phase 1: checked %s\n" uu____4552);
                    (let uu____4553 =
                       FStar_TypeChecker_Env.should_verify env1 in
                     if uu____4553
                     then check_top_level_let_rec env1 lax_top
                     else (lax_top, l, g)))
             else check_top_level_let_rec env1 top))
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____4562),uu____4563) ->
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
        let uu____4589 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____4679))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____4739))::(uu____4740,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____4741))::
              (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____4814 ->
              FStar_Exn.raise
                (FStar_Errors.Error ("synth_by_tactic: bad application", rng)) in
        match uu____4589 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____4898 = FStar_TypeChecker_Env.expected_typ env in
                  (match uu____4898 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____4904 =
                         let uu____4905 =
                           let uu____4910 =
                             FStar_TypeChecker_Env.get_range env in
                           ("synth_by_tactic: need a type annotation when no expected type is present",
                             uu____4910) in
                         FStar_Errors.Error uu____4905 in
                       FStar_Exn.raise uu____4904) in
            let uu____4913 = FStar_TypeChecker_Env.clear_expected_typ env in
            (match uu____4913 with
             | (env',uu____4927) ->
                 let uu____4932 = tc_term env' typ in
                 (match uu____4932 with
                  | (typ1,uu____4946,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____4949 = tc_tactic env' tau in
                        match uu____4949 with
                        | (tau1,uu____4963,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let uu____4967 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Tac") in
                              if uu____4967
                              then
                                let uu____4968 =
                                  FStar_Syntax_Print.term_to_string tau1 in
                                let uu____4969 =
                                  FStar_Syntax_Print.term_to_string typ1 in
                                FStar_Util.print2
                                  "Running tactic %s at return type %s\n"
                                  uu____4968 uu____4969
                              else ());
                             (let t =
                                env.FStar_TypeChecker_Env.synth env' typ1
                                  tau1 in
                              (let uu____4973 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "Tac") in
                               if uu____4973
                               then
                                 let uu____4974 =
                                   FStar_Syntax_Print.term_to_string t in
                                 FStar_Util.print1 "Got %s\n" uu____4974
                               else ());
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____4977 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng in
                               tc_term env uu____4977)))))))
and tc_tactic:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___104_4981 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___104_4981.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___104_4981.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___104_4981.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___104_4981.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___104_4981.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___104_4981.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___104_4981.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___104_4981.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___104_4981.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___104_4981.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___104_4981.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___104_4981.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___104_4981.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___104_4981.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___104_4981.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___104_4981.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___104_4981.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___104_4981.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___104_4981.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___104_4981.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.type_of =
            (uu___104_4981.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___104_4981.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___104_4981.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___104_4981.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___104_4981.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___104_4981.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___104_4981.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___104_4981.FStar_TypeChecker_Env.identifier_info)
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
        let uu___105_4985 = env in
        {
          FStar_TypeChecker_Env.solver =
            (uu___105_4985.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___105_4985.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___105_4985.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___105_4985.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___105_4985.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___105_4985.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___105_4985.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___105_4985.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___105_4985.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___105_4985.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___105_4985.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___105_4985.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___105_4985.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___105_4985.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___105_4985.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___105_4985.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___105_4985.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___105_4985.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___105_4985.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___105_4985.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.type_of =
            (uu___105_4985.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___105_4985.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___105_4985.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___105_4985.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___105_4985.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___105_4985.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___105_4985.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___105_4985.FStar_TypeChecker_Env.identifier_info)
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
          let uu____5001 = tc_tactic env tactic in
          (match uu____5001 with
           | (tactic1,uu____5011,uu____5012) ->
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
        let uu____5051 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____5051 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____5072 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____5072
              then FStar_Util.Inl t1
              else
                (let uu____5078 =
                   let uu____5079 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____5079 in
                 FStar_Util.Inr uu____5078) in
            let is_data_ctor uu___90_5089 =
              match uu___90_5089 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____5092) -> true
              | uu____5099 -> false in
            let uu____5102 =
              (is_data_ctor dc) &&
                (let uu____5104 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____5104) in
            if uu____5102
            then
              let uu____5111 =
                let uu____5112 =
                  let uu____5117 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____5118 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____5117, uu____5118) in
                FStar_Errors.Error uu____5112 in
              FStar_Exn.raise uu____5111
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____5135 =
            let uu____5136 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____5136 in
          failwith uu____5135
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____5170 =
              let uu____5171 = FStar_Syntax_Subst.compress t1 in
              uu____5171.FStar_Syntax_Syntax.n in
            match uu____5170 with
            | FStar_Syntax_Syntax.Tm_arrow uu____5174 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____5187 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___106_5225 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___106_5225.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___106_5225.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___106_5225.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____5277 =
            let uu____5290 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____5290 with
            | FStar_Pervasives_Native.None  ->
                let uu____5305 = FStar_Syntax_Util.type_u () in
                (match uu____5305 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____5277 with
           | (t,uu____5342,g0) ->
               let uu____5356 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____5356 with
                | (e1,uu____5376,g1) ->
                    let uu____5390 =
                      let uu____5391 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____5391
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____5392 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____5390, uu____5392)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____5394 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____5407 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____5407)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____5394 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___107_5426 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___107_5426.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___107_5426.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____5429 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____5429 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____5450 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____5450
                       then FStar_Util.Inl t1
                       else
                         (let uu____5456 =
                            let uu____5457 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____5457 in
                          FStar_Util.Inr uu____5456) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____5463;
             FStar_Syntax_Syntax.vars = uu____5464;_},uu____5465)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____5470 =
            let uu____5471 =
              let uu____5476 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____5476) in
            FStar_Errors.Error uu____5471 in
          FStar_Exn.raise uu____5470
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____5484 =
            let uu____5485 =
              let uu____5490 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____5490) in
            FStar_Errors.Error uu____5485 in
          FStar_Exn.raise uu____5484
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____5498;
             FStar_Syntax_Syntax.vars = uu____5499;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____5508 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5508 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____5531 =
                     let uu____5532 =
                       let uu____5537 =
                         let uu____5538 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____5539 =
                           FStar_Util.string_of_int (FStar_List.length us1) in
                         let uu____5540 =
                           FStar_Util.string_of_int (FStar_List.length us') in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____5538 uu____5539 uu____5540 in
                       let uu____5541 = FStar_TypeChecker_Env.get_range env1 in
                       (uu____5537, uu____5541) in
                     FStar_Errors.Error uu____5532 in
                   FStar_Exn.raise uu____5531)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____5557 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____5561 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____5561 us1 in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5563 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5563 with
           | ((us,t),range) ->
               ((let uu____5586 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____5586
                 then
                   let uu____5587 =
                     let uu____5588 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____5588 in
                   let uu____5589 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____5590 = FStar_Range.string_of_range range in
                   let uu____5591 = FStar_Range.string_of_use_range range in
                   let uu____5592 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____5587 uu____5589 uu____5590 uu____5591 uu____5592
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____5597 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____5597 us in
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
          let uu____5621 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____5621 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____5635 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____5635 with
                | (env2,uu____5649) ->
                    let uu____5654 = tc_binders env2 bs1 in
                    (match uu____5654 with
                     | (bs2,env3,g,us) ->
                         let uu____5673 = tc_comp env3 c1 in
                         (match uu____5673 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___108_5692 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___108_5692.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___108_5692.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____5701 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____5701 in
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
          let uu____5720 =
            let uu____5725 =
              let uu____5726 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5726] in
            FStar_Syntax_Subst.open_term uu____5725 phi in
          (match uu____5720 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____5736 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____5736 with
                | (env2,uu____5750) ->
                    let uu____5755 =
                      let uu____5768 = FStar_List.hd x1 in
                      tc_binder env2 uu____5768 in
                    (match uu____5755 with
                     | (x2,env3,f1,u) ->
                         ((let uu____5796 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____5796
                           then
                             let uu____5797 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____5798 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____5799 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____5797 uu____5798 uu____5799
                           else ());
                          (let uu____5801 = FStar_Syntax_Util.type_u () in
                           match uu____5801 with
                           | (t_phi,uu____5813) ->
                               let uu____5814 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____5814 with
                                | (phi2,uu____5828,f2) ->
                                    let e1 =
                                      let uu___109_5833 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___109_5833.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___109_5833.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____5840 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____5840 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____5853) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____5876 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____5876
            then
              let uu____5877 =
                FStar_Syntax_Print.term_to_string
                  (let uu___110_5880 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___110_5880.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___110_5880.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____5877
            else ());
           (let uu____5886 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____5886 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____5899 ->
          let uu____5900 =
            let uu____5901 = FStar_Syntax_Print.term_to_string top in
            let uu____5902 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____5901
              uu____5902 in
          failwith uu____5900
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
      | FStar_Const.Const_bool uu____5911 -> FStar_Syntax_Util.t_bool
      | FStar_Const.Const_int (uu____5912,FStar_Pervasives_Native.None ) ->
          FStar_Syntax_Syntax.t_int
      | FStar_Const.Const_int
          (uu____5923,FStar_Pervasives_Native.Some uu____5924) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____5939 -> FStar_Syntax_Syntax.t_string
      | FStar_Const.Const_float uu____5946 -> FStar_Syntax_Syntax.t_float
      | FStar_Const.Const_char uu____5947 -> FStar_Syntax_Syntax.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____5948 -> FStar_Syntax_Syntax.t_range
      | uu____5949 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____5966) ->
          let uu____5975 = FStar_Syntax_Util.type_u () in
          (match uu____5975 with
           | (k,u) ->
               let uu____5988 = tc_check_tot_or_gtot_term env t k in
               (match uu____5988 with
                | (t1,uu____6002,g) ->
                    let uu____6004 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____6004, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____6006) ->
          let uu____6015 = FStar_Syntax_Util.type_u () in
          (match uu____6015 with
           | (k,u) ->
               let uu____6028 = tc_check_tot_or_gtot_term env t k in
               (match uu____6028 with
                | (t1,uu____6042,g) ->
                    let uu____6044 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____6044, u, g)))
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
            let uu____6052 =
              let uu____6053 =
                let uu____6054 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____6054 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____6053 in
            uu____6052 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____6057 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____6057 with
           | (tc1,uu____6071,f) ->
               let uu____6073 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____6073 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____6117 =
                        let uu____6118 = FStar_Syntax_Subst.compress head3 in
                        uu____6118.FStar_Syntax_Syntax.n in
                      match uu____6117 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____6121,us) -> us
                      | uu____6127 -> [] in
                    let uu____6128 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____6128 with
                     | (uu____6149,args1) ->
                         let uu____6171 =
                           let uu____6190 = FStar_List.hd args1 in
                           let uu____6203 = FStar_List.tl args1 in
                           (uu____6190, uu____6203) in
                         (match uu____6171 with
                          | (res,args2) ->
                              let uu____6268 =
                                let uu____6277 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___91_6305  ->
                                          match uu___91_6305 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____6313 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____6313 with
                                               | (env1,uu____6325) ->
                                                   let uu____6330 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____6330 with
                                                    | (e1,uu____6342,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____6277
                                  FStar_List.unzip in
                              (match uu____6268 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___111_6381 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___111_6381.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___111_6381.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____6385 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____6385 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____6389 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____6389))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____6397 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____6398 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____6408 = aux u3 in FStar_Syntax_Syntax.U_succ uu____6408
        | FStar_Syntax_Syntax.U_max us ->
            let uu____6412 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____6412
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____6417 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____6417 FStar_Pervasives_Native.snd
         | uu____6426 -> aux u)
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
            let uu____6450 =
              let uu____6451 =
                let uu____6456 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____6456, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____6451 in
            FStar_Exn.raise uu____6450 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____6546 bs2 bs_expected1 =
              match uu____6546 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____6714)) ->
                             let uu____6719 =
                               let uu____6720 =
                                 let uu____6725 =
                                   let uu____6726 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____6726 in
                                 let uu____6727 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____6725, uu____6727) in
                               FStar_Errors.Error uu____6720 in
                             FStar_Exn.raise uu____6719
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____6728),FStar_Pervasives_Native.None ) ->
                             let uu____6733 =
                               let uu____6734 =
                                 let uu____6739 =
                                   let uu____6740 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____6740 in
                                 let uu____6741 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____6739, uu____6741) in
                               FStar_Errors.Error uu____6734 in
                             FStar_Exn.raise uu____6733
                         | uu____6742 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____6748 =
                           let uu____6753 =
                             let uu____6754 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____6754.FStar_Syntax_Syntax.n in
                           match uu____6753 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____6761 ->
                               ((let uu____6763 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____6763
                                 then
                                   let uu____6764 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____6764
                                 else ());
                                (let uu____6766 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____6766 with
                                 | (t,uu____6778,g1) ->
                                     let g2 =
                                       let uu____6781 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____6782 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____6781
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____6782 in
                                     let g3 =
                                       let uu____6784 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____6784 in
                                     (t, g3))) in
                         match uu____6748 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___112_6812 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___112_6812.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___112_6812.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____6825 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____6825 in
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
                  | uu____6979 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____6986 = tc_binders env1 bs in
                  match uu____6986 with
                  | (bs1,envbody,g,uu____7020) ->
                      let uu____7021 =
                        let uu____7034 =
                          let uu____7035 = FStar_Syntax_Subst.compress body1 in
                          uu____7035.FStar_Syntax_Syntax.n in
                        match uu____7034 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____7053) ->
                            let uu____7100 = tc_comp envbody c in
                            (match uu____7100 with
                             | (c1,uu____7120,g') ->
                                 let uu____7122 =
                                   tc_tactic_opt envbody tacopt in
                                 let uu____7125 =
                                   FStar_TypeChecker_Rel.conj_guard g g' in
                                 ((FStar_Pervasives_Native.Some c1),
                                   uu____7122, body1, uu____7125))
                        | uu____7130 ->
                            (FStar_Pervasives_Native.None,
                              FStar_Pervasives_Native.None, body1, g) in
                      (match uu____7021 with
                       | (copt,tacopt,body2,g1) ->
                           (FStar_Pervasives_Native.None, bs1, [], copt,
                             tacopt, envbody, body2, g1))))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____7218 =
                    let uu____7219 = FStar_Syntax_Subst.compress t2 in
                    uu____7219.FStar_Syntax_Syntax.n in
                  match uu____7218 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____7246 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____7268 -> failwith "Impossible");
                       (let uu____7275 = tc_binders env1 bs in
                        match uu____7275 with
                        | (bs1,envbody,g,uu____7311) ->
                            let uu____7312 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____7312 with
                             | (envbody1,uu____7344) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None,
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____7357;
                         FStar_Syntax_Syntax.pos = uu____7358;
                         FStar_Syntax_Syntax.vars = uu____7359;_},uu____7360)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____7402 -> failwith "Impossible");
                       (let uu____7409 = tc_binders env1 bs in
                        match uu____7409 with
                        | (bs1,envbody,g,uu____7445) ->
                            let uu____7446 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____7446 with
                             | (envbody1,uu____7478) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None,
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____7492) ->
                      let uu____7497 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____7497 with
                       | (uu____7546,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, tacopt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____7596 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____7596 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____7700 c_expected2 =
                               match uu____7700 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____7815 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____7815)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____7846 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____7846 in
                                        let uu____7847 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____7847)
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
                                               let uu____7919 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____7919 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____7940 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____7940 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____7988 =
                                                           let uu____8019 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____8019,
                                                             subst2) in
                                                         handle_more
                                                           uu____7988
                                                           c_expected4))
                                           | uu____8036 ->
                                               let uu____8037 =
                                                 let uu____8038 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____8038 in
                                               fail uu____8037 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____8068 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____8068 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___113_8127 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___113_8127.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___113_8127.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___113_8127.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___113_8127.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___113_8127.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___113_8127.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___113_8127.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___113_8127.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___113_8127.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___113_8127.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___113_8127.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___113_8127.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___113_8127.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___113_8127.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___113_8127.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___113_8127.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___113_8127.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___113_8127.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___113_8127.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___113_8127.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___113_8127.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___113_8127.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___113_8127.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___113_8127.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___113_8127.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___113_8127.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___113_8127.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___113_8127.FStar_TypeChecker_Env.identifier_info)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____8166  ->
                                     fun uu____8167  ->
                                       match (uu____8166, uu____8167) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____8212 =
                                             let uu____8219 =
                                               let uu____8220 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____8220
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____8219 t3 in
                                           (match uu____8212 with
                                            | (t4,uu____8242,uu____8243) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____8253 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___114_8256
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___114_8256.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___114_8256.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____8253 ::
                                                        letrec_binders
                                                  | uu____8257 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____8262 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____8262 with
                            | (envbody,bs1,g,c) ->
                                let uu____8317 = mk_letrec_env envbody bs1 c in
                                (match uu____8317 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       FStar_Pervasives_Native.None,
                                       envbody2, body1, g))))
                  | uu____8369 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____8394 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____8394
                      else
                        (let uu____8396 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1 in
                         match uu____8396 with
                         | (uu____8443,bs1,uu____8445,c_opt,tacopt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, tacopt, envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____8472 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____8472 with
          | (env1,topt) ->
              ((let uu____8492 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____8492
                then
                  let uu____8493 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____8493
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____8497 = expected_function_typ1 env1 topt body in
                match uu____8497 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____8546 =
                      tc_term
                        (let uu___115_8555 = envbody in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___115_8555.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___115_8555.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___115_8555.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___115_8555.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___115_8555.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___115_8555.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___115_8555.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___115_8555.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___115_8555.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___115_8555.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___115_8555.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___115_8555.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___115_8555.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___115_8555.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___115_8555.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___115_8555.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___115_8555.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___115_8555.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___115_8555.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.type_of =
                             (uu___115_8555.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___115_8555.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___115_8555.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___115_8555.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___115_8555.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___115_8555.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___115_8555.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___115_8555.FStar_TypeChecker_Env.identifier_info)
                         }) body1 in
                    (match uu____8546 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body in
                         ((let uu____8567 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits") in
                           if uu____8567
                           then
                             let uu____8568 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits) in
                             let uu____8581 =
                               let uu____8582 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____8582 in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____8568 uu____8581
                           else ());
                          (let uu____8584 =
                             let uu____8591 =
                               let uu____8596 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               (body2, uu____8596) in
                             check_expected_effect
                               (let uu___116_8603 = envbody in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___116_8603.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___116_8603.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___116_8603.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___116_8603.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___116_8603.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___116_8603.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___116_8603.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___116_8603.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___116_8603.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___116_8603.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___116_8603.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___116_8603.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___116_8603.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___116_8603.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___116_8603.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___116_8603.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___116_8603.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___116_8603.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___116_8603.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___116_8603.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___116_8603.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___116_8603.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___116_8603.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___116_8603.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___116_8603.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___116_8603.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___116_8603.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___116_8603.FStar_TypeChecker_Env.identifier_info)
                                }) c_opt uu____8591 in
                           match uu____8584 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard in
                               let guard2 =
                                 let uu____8615 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____8617 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1 in
                                      Prims.op_Negation uu____8617) in
                                 if uu____8615
                                 then
                                   let uu____8618 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1 in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____8618
                                 else
                                   (let guard2 =
                                      let uu____8621 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1 in
                                      FStar_TypeChecker_Rel.close_guard env1
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____8621 in
                                    guard2) in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1 in
                               let e =
                                 FStar_Syntax_Util.abs bs1 body3
                                   (FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         (FStar_Util.dflt cbody1 c_opt))) in
                               let uu____8630 =
                                 match tfun_opt with
                                 | FStar_Pervasives_Native.Some t ->
                                     let t1 = FStar_Syntax_Subst.compress t in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____8651 -> (e, t1, guard2)
                                      | uu____8664 ->
                                          let uu____8665 =
                                            FStar_TypeChecker_Util.check_and_ascribe
                                              env1 e tfun_computed t1 in
                                          (match uu____8665 with
                                           | (e1,guard') ->
                                               let uu____8678 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard' in
                                               (e1, t1, uu____8678)))
                                 | FStar_Pervasives_Native.None  ->
                                     (e, tfun_computed, guard2) in
                               (match uu____8630 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1 in
                                    let uu____8692 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        FStar_Pervasives_Native.None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3 in
                                    (match uu____8692 with
                                     | (c1,g1) -> (e1, c1, g1))))))))
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
              (let uu____8741 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____8741
               then
                 let uu____8742 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____8743 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____8742
                   uu____8743
               else ());
              (let monadic_application uu____8800 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____8800 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___117_8859 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___117_8859.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___117_8859.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___117_8859.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____8860 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
                       | uu____8875 ->
                           let g =
                             let uu____8883 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____8883
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____8884 =
                             let uu____8885 =
                               let uu____8888 =
                                 let uu____8889 =
                                   let uu____8890 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____8890 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____8889 in
                               FStar_Syntax_Syntax.mk_Total uu____8888 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____8885 in
                           (uu____8884, g) in
                     (match uu____8860 with
                      | (cres2,guard1) ->
                          ((let uu____8904 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____8904
                            then
                              let uu____8905 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____8905
                            else ());
                           (let cres3 =
                              let uu____8908 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____8908
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
                                   fun uu____8942  ->
                                     match uu____8942 with
                                     | ((e,q),x,c) ->
                                         let uu____8975 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____8975
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
                              let uu____8987 =
                                let uu____8988 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____8988.FStar_Syntax_Syntax.n in
                              match uu____8987 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____8992 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____9013  ->
                                         match uu____9013 with
                                         | (arg,uu____9027,uu____9028) -> arg
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
                                (let uu____9038 =
                                   let map_fun uu____9100 =
                                     match uu____9100 with
                                     | ((e,q),uu____9135,c) ->
                                         let uu____9145 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____9145
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
                                            let uu____9195 =
                                              let uu____9200 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____9200, q) in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____9195)) in
                                   let uu____9229 =
                                     let uu____9254 =
                                       let uu____9277 =
                                         let uu____9292 =
                                           let uu____9301 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____9301,
                                             FStar_Pervasives_Native.None,
                                             chead1) in
                                         uu____9292 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____9277 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____9254 in
                                   match uu____9229 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____9474 =
                                         let uu____9475 =
                                           FStar_List.hd reverse_args in
                                         FStar_Pervasives_Native.fst
                                           uu____9475 in
                                       let uu____9484 =
                                         let uu____9491 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____9491 in
                                       (lifted_args, uu____9474, uu____9484) in
                                 match uu____9038 with
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
                                     let bind_lifted_args e uu___92_9594 =
                                       match uu___92_9594 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____9649 =
                                               let uu____9652 =
                                                 let uu____9653 =
                                                   let uu____9666 =
                                                     let uu____9667 =
                                                       let uu____9668 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____9668] in
                                                     FStar_Syntax_Subst.close
                                                       uu____9667 e in
                                                   ((false, [lb]),
                                                     uu____9666) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____9653 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____9652 in
                                             uu____9649
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
                            let uu____9698 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp1
                                guard1 in
                            match uu____9698 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____9789 bs args1 =
                 match uu____9789 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____9936))::rest,
                         (uu____9938,FStar_Pervasives_Native.None )::uu____9939)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t in
                          let uu____10000 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____10000 with
                           | (varg,uu____10020,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____10042 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____10042) in
                               let uu____10043 =
                                 let uu____10078 =
                                   let uu____10093 =
                                     let uu____10106 =
                                       let uu____10107 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____10107
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____10106) in
                                   uu____10093 :: outargs in
                                 let uu____10126 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____10078, (arg :: arg_rets),
                                   uu____10126, fvs) in
                               tc_args head_info uu____10043 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____10228),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____10229)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____10242 ->
                                FStar_Exn.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___118_10253 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___118_10253.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___118_10253.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____10255 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____10255
                             then
                               let uu____10256 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____10256
                             else ());
                            (let targ1 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___119_10261 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___119_10261.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___119_10261.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___119_10261.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___119_10261.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___119_10261.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___119_10261.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___119_10261.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___119_10261.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___119_10261.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___119_10261.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___119_10261.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___119_10261.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___119_10261.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___119_10261.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___119_10261.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___119_10261.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___119_10261.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___119_10261.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___119_10261.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___119_10261.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___119_10261.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___119_10261.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___119_10261.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___119_10261.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___119_10261.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___119_10261.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___119_10261.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___119_10261.FStar_TypeChecker_Env.identifier_info)
                               } in
                             (let uu____10263 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____10263
                              then
                                let uu____10264 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____10265 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____10266 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____10264 uu____10265 uu____10266
                              else ());
                             (let uu____10268 = tc_term env2 e in
                              match uu____10268 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____10295 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____10295 in
                                  let uu____10296 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____10296
                                  then
                                    let subst2 =
                                      let uu____10304 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____10304
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
                      | (uu____10398,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____10434) ->
                          let uu____10485 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____10485 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____10519 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____10519
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____10544 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____10544 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____10567 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____10567
                                            then
                                              let uu____10568 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____10568
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____10610 when Prims.op_Negation norm1
                                     ->
                                     let uu____10611 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____10611
                                 | uu____10612 ->
                                     let uu____10613 =
                                       let uu____10614 =
                                         let uu____10619 =
                                           let uu____10620 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____10621 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____10620 uu____10621 in
                                         let uu____10628 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____10619, uu____10628) in
                                       FStar_Errors.Error uu____10614 in
                                     FStar_Exn.raise uu____10613 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____10647 =
                   let uu____10648 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____10648.FStar_Syntax_Syntax.n in
                 match uu____10647 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____10659 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____10760 = tc_term env1 e in
                           (match uu____10760 with
                            | (e1,c,g_e) ->
                                let uu____10782 = tc_args1 env1 tl1 in
                                (match uu____10782 with
                                 | (args2,comps,g_rest) ->
                                     let uu____10822 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____10822))) in
                     let uu____10843 = tc_args1 env args in
                     (match uu____10843 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____10880 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____10918  ->
                                      match uu____10918 with
                                      | (uu____10931,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____10880 in
                          let ml_or_tot t r1 =
                            let uu____10948 = FStar_Options.ml_ish () in
                            if uu____10948
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____10951 =
                              let uu____10954 =
                                let uu____10955 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____10955
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____10954 in
                            ml_or_tot uu____10951 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____10968 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____10968
                            then
                              let uu____10969 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____10970 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____10971 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____10969 uu____10970 uu____10971
                            else ());
                           (let uu____10974 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____10974);
                           (let comp =
                              let uu____10976 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____10987  ->
                                   fun out  ->
                                     match uu____10987 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____10976 in
                            let uu____11001 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____11004 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____11001, comp, uu____11004))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____11007;
                        FStar_Syntax_Syntax.pos = uu____11008;
                        FStar_Syntax_Syntax.vars = uu____11009;_},uu____11010)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____11131 = tc_term env1 e in
                           (match uu____11131 with
                            | (e1,c,g_e) ->
                                let uu____11153 = tc_args1 env1 tl1 in
                                (match uu____11153 with
                                 | (args2,comps,g_rest) ->
                                     let uu____11193 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____11193))) in
                     let uu____11214 = tc_args1 env args in
                     (match uu____11214 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____11251 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____11289  ->
                                      match uu____11289 with
                                      | (uu____11302,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____11251 in
                          let ml_or_tot t r1 =
                            let uu____11319 = FStar_Options.ml_ish () in
                            if uu____11319
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____11322 =
                              let uu____11325 =
                                let uu____11326 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____11326
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____11325 in
                            ml_or_tot uu____11322 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____11339 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____11339
                            then
                              let uu____11340 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____11341 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____11342 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____11340 uu____11341 uu____11342
                            else ());
                           (let uu____11345 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____11345);
                           (let comp =
                              let uu____11347 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____11358  ->
                                   fun out  ->
                                     match uu____11358 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____11347 in
                            let uu____11372 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                FStar_Pervasives_Native.None r in
                            let uu____11375 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____11372, comp, uu____11375))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____11396 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____11396 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____11461) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____11467,uu____11468) -> check_function_app t
                 | uu____11509 ->
                     let uu____11510 =
                       let uu____11511 =
                         let uu____11516 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____11516, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____11511 in
                     FStar_Exn.raise uu____11510 in
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
                  let uu____11586 =
                    FStar_List.fold_left2
                      (fun uu____11629  ->
                         fun uu____11630  ->
                           fun uu____11631  ->
                             match (uu____11629, uu____11630, uu____11631)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    FStar_Exn.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____11699 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____11699 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____11717 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____11717 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____11721 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____11721)
                                              &&
                                              (let uu____11723 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____11723)) in
                                       let uu____11724 =
                                         let uu____11733 =
                                           let uu____11742 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____11742] in
                                         FStar_List.append seen uu____11733 in
                                       let uu____11749 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____11724, uu____11749, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____11586 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r in
                       let c1 =
                         if ghost
                         then
                           let uu____11785 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____11785
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____11787 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____11787 with | (c2,g) -> (e, c2, g)))
              | uu____11804 ->
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
        let uu____11838 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____11838 with
        | (pattern,when_clause,branch_exp) ->
            let uu____11874 = branch1 in
            (match uu____11874 with
             | (cpat,uu____11906,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____11958 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 in
                   match uu____11958 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____11987 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____11987
                         then
                           let uu____11988 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____11989 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____11988 uu____11989
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____11992 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____11992 with
                         | (env1,uu____12012) ->
                             let env11 =
                               let uu___120_12018 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___120_12018.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___120_12018.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___120_12018.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___120_12018.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___120_12018.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___120_12018.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___120_12018.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___120_12018.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___120_12018.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___120_12018.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___120_12018.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___120_12018.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___120_12018.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___120_12018.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___120_12018.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___120_12018.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___120_12018.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___120_12018.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___120_12018.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___120_12018.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___120_12018.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___120_12018.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___120_12018.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___120_12018.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___120_12018.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___120_12018.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___120_12018.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___120_12018.FStar_TypeChecker_Env.identifier_info)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____12021 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____12021
                               then
                                 let uu____12022 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____12023 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____12022 uu____12023
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t in
                               let uu____12026 =
                                 tc_tot_or_gtot_term env12 exp in
                               match uu____12026 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___121_12049 = g in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___121_12049.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___121_12049.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___121_12049.FStar_TypeChecker_Env.implicits)
                                     } in
                                   let uu____12050 =
                                     let g' =
                                       FStar_TypeChecker_Rel.teq env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t in
                                     let g2 =
                                       FStar_TypeChecker_Rel.conj_guard g1 g' in
                                     let env13 =
                                       FStar_TypeChecker_Env.set_range env12
                                         exp1.FStar_Syntax_Syntax.pos in
                                     let uu____12054 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         env13 g2 in
                                     FStar_All.pipe_right uu____12054
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1 in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____12071 =
                                       let uu____12072 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____12072 in
                                     if uu____12071
                                     then
                                       let unresolved =
                                         let uu____12084 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____12084
                                           FStar_Util.set_elements in
                                       let uu____12111 =
                                         let uu____12112 =
                                           let uu____12117 =
                                             let uu____12118 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____12119 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____12120 =
                                               let uu____12121 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____12139  ->
                                                         match uu____12139
                                                         with
                                                         | (u,uu____12145) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____12121
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____12118 uu____12119
                                               uu____12120 in
                                           (uu____12117,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____12112 in
                                       FStar_Exn.raise uu____12111
                                     else ());
                                    (let uu____12150 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____12150
                                     then
                                       let uu____12151 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____12151
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____12160 =
                   let uu____12167 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____12167
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____12160 with
                  | (scrutinee_env,uu____12191) ->
                      let uu____12196 = tc_pat true pat_t pattern in
                      (match uu____12196 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____12234 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____12256 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____12256
                                 then
                                   FStar_Exn.raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____12270 =
                                      let uu____12277 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool in
                                      tc_term uu____12277 e in
                                    match uu____12270 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g)) in
                           (match uu____12234 with
                            | (when_clause1,g_when) ->
                                let uu____12311 = tc_term pat_env branch_exp in
                                (match uu____12311 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some w ->
                                           let uu____12343 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_41  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_41) uu____12343 in
                                     let uu____12346 =
                                       let eqs =
                                         let uu____12356 =
                                           let uu____12357 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____12357 in
                                         if uu____12356
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____12364 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____12381 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____12382 ->
                                                FStar_Pervasives_Native.None
                                            | uu____12383 ->
                                                let uu____12384 =
                                                  let uu____12385 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____12385 pat_t
                                                    scrutinee_tm e in
                                                FStar_Pervasives_Native.Some
                                                  uu____12384) in
                                       let uu____12386 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch in
                                       match uu____12386 with
                                       | (c1,g_branch1) ->
                                           let uu____12401 =
                                             match (eqs, when_condition) with
                                             | uu____12414 when
                                                 let uu____12423 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation
                                                   uu____12423
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
                                                 let uu____12435 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____12436 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____12435, uu____12436)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____12445 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____12445 in
                                                 let uu____12446 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____12447 =
                                                   let uu____12448 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____12448 g_when in
                                                 (uu____12446, uu____12447)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____12456 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____12456, g_when) in
                                           (match uu____12401 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____12468 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____12469 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____12468, uu____12469,
                                                  g_branch1)) in
                                     (match uu____12346 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____12490 =
                                              let uu____12491 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____12491 in
                                            if uu____12490
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____12521 =
                                                     let uu____12522 =
                                                       let uu____12523 =
                                                         let uu____12526 =
                                                           let uu____12533 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____12533 in
                                                         FStar_Pervasives_Native.snd
                                                           uu____12526 in
                                                       FStar_List.length
                                                         uu____12523 in
                                                     uu____12522 >
                                                       (Prims.parse_int "1") in
                                                   if uu____12521
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____12539 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____12539 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____12560 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None in
                                                         let disc1 =
                                                           let uu____12575 =
                                                             let uu____12576
                                                               =
                                                               let uu____12577
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____12577] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____12576 in
                                                           uu____12575
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____12580 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool in
                                                         [uu____12580]
                                                   else [] in
                                                 let fail uu____12585 =
                                                   let uu____12586 =
                                                     let uu____12587 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____12588 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____12589 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____12587
                                                       uu____12588
                                                       uu____12589 in
                                                   failwith uu____12586 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____12600) ->
                                                       head_constructor t1
                                                   | uu____12605 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____12607 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____12607
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____12610 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____12627;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____12628;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____12629;_},uu____12630)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____12667 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____12669 =
                                                       let uu____12670 =
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____12670
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____12669]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____12671 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____12679 =
                                                       let uu____12680 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____12680 in
                                                     if uu____12679
                                                     then []
                                                     else
                                                       (let uu____12684 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____12684)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____12687 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____12689 =
                                                       let uu____12690 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____12690 in
                                                     if uu____12689
                                                     then []
                                                     else
                                                       (let uu____12694 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____12694)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____12720 =
                                                       let uu____12721 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____12721 in
                                                     if uu____12720
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____12728 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____12760
                                                                     ->
                                                                    match uu____12760
                                                                    with
                                                                    | 
                                                                    (ei,uu____12770)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____12776
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____12776
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____12797
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____12811
                                                                    =
                                                                    let uu____12812
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____12813
                                                                    =
                                                                    let uu____12814
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____12814] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____12812
                                                                    uu____12813 in
                                                                    uu____12811
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____12728
                                                            FStar_List.flatten in
                                                        let uu____12823 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____12823
                                                          sub_term_guards)
                                                 | uu____12826 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____12838 =
                                                   let uu____12839 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____12839 in
                                                 if uu____12838
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____12842 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____12842 in
                                                    let uu____12847 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____12847 with
                                                    | (k,uu____12853) ->
                                                        let uu____12854 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____12854
                                                         with
                                                         | (t1,uu____12862,uu____12863)
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
                                          ((let uu____12869 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____12869
                                            then
                                              let uu____12870 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____12870
                                            else ());
                                           (let uu____12872 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____12872, branch_guard, c1,
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
          let uu____12898 = check_let_bound_def true env1 lb in
          (match uu____12898 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____12920 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____12937 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____12937, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____12940 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____12940
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____12944 =
                      let uu____12953 =
                        let uu____12964 =
                          let uu____12973 =
                            let uu____12986 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1,
                              uu____12986) in
                          [uu____12973] in
                        FStar_TypeChecker_Util.generalize env1 uu____12964 in
                      FStar_List.hd uu____12953 in
                    match uu____12944 with
                    | (uu____13035,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____12920 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____13049 =
                      let uu____13056 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____13056
                      then
                        let uu____13063 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____13063 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____13086 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____13086
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____13087 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____13087, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____13097 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____13097
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.NoFullNorm] env1) in
                          let e21 =
                            let uu____13105 =
                              FStar_Syntax_Util.is_pure_comp c in
                            if uu____13105
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
                    (match uu____13049 with
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
                         let uu____13127 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), e21))
                             FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         (uu____13127,
                           (FStar_Syntax_Util.lcomp_of_comp cres),
                           FStar_TypeChecker_Rel.trivial_guard))))
      | uu____13142 -> failwith "Impossible"
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
            let uu___122_13173 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___122_13173.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___122_13173.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___122_13173.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___122_13173.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___122_13173.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___122_13173.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___122_13173.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___122_13173.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___122_13173.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___122_13173.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___122_13173.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___122_13173.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___122_13173.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___122_13173.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___122_13173.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___122_13173.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___122_13173.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___122_13173.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___122_13173.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___122_13173.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.type_of =
                (uu___122_13173.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___122_13173.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___122_13173.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___122_13173.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___122_13173.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___122_13173.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___122_13173.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___122_13173.FStar_TypeChecker_Env.identifier_info)
            } in
          let uu____13174 =
            let uu____13185 =
              let uu____13186 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____13186 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____13185 lb in
          (match uu____13174 with
           | (e1,uu____13208,c1,g1,annotated) ->
               let x =
                 let uu___123_13213 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___123_13213.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___123_13213.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____13214 =
                 let uu____13219 =
                   let uu____13220 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____13220] in
                 FStar_Syntax_Subst.open_term uu____13219 e2 in
               (match uu____13214 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = FStar_Pervasives_Native.fst xbinder in
                    let uu____13239 =
                      let uu____13246 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____13246 e21 in
                    (match uu____13239 with
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
                           let uu____13265 =
                             let uu____13268 =
                               let uu____13269 =
                                 let uu____13282 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____13282) in
                               FStar_Syntax_Syntax.Tm_let uu____13269 in
                             FStar_Syntax_Syntax.mk uu____13268 in
                           uu____13265 FStar_Pervasives_Native.None
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____13296 =
                             let uu____13297 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____13298 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____13297
                               c1.FStar_Syntax_Syntax.res_typ uu____13298 e11 in
                           FStar_All.pipe_left
                             (fun _0_42  ->
                                FStar_TypeChecker_Common.NonTrivial _0_42)
                             uu____13296 in
                         let g21 =
                           let uu____13300 =
                             let uu____13301 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____13301 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____13300 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____13303 =
                           let uu____13304 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____13304 in
                         if uu____13303
                         then
                           let tt =
                             let uu____13314 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____13314
                               FStar_Option.get in
                           ((let uu____13320 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____13320
                             then
                               let uu____13321 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____13322 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____13321 uu____13322
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape FStar_Pervasives_Native.None
                                env2 [x1] cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____13327 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____13327
                             then
                               let uu____13328 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____13329 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____13328 uu____13329
                             else ());
                            (e4,
                              ((let uu___124_13332 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___124_13332.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___124_13332.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___124_13332.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____13333 -> failwith "Impossible"
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
          let uu____13365 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____13365 with
           | (lbs1,e21) ->
               let uu____13384 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____13384 with
                | (env0,topt) ->
                    let uu____13403 = build_let_rec_env true env0 lbs1 in
                    (match uu____13403 with
                     | (lbs2,rec_env) ->
                         let uu____13422 = check_let_recs rec_env lbs2 in
                         (match uu____13422 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____13442 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____13442
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____13448 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____13448
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
                                              lb.FStar_Syntax_Syntax.lbname
                                              lb.FStar_Syntax_Syntax.lbunivs
                                              lb.FStar_Syntax_Syntax.lbtyp
                                              lb.FStar_Syntax_Syntax.lbeff
                                              lbdef))
                                else
                                  (let ecs =
                                     let uu____13493 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____13533 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____13533))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____13493 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____13571  ->
                                           match uu____13571 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____13603 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____13603 in
                              let uu____13608 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                              (match uu____13608 with
                               | (lbs5,e22) ->
                                   ((let uu____13628 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1 in
                                     FStar_All.pipe_right uu____13628
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____13629 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos in
                                     (uu____13629, cres,
                                       FStar_TypeChecker_Rel.trivial_guard))))))))
      | uu____13642 -> failwith "Impossible"
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
          let uu____13674 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____13674 with
           | (lbs1,e21) ->
               let uu____13693 =
                 FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____13693 with
                | (env0,topt) ->
                    let uu____13712 = build_let_rec_env false env0 lbs1 in
                    (match uu____13712 with
                     | (lbs2,rec_env) ->
                         let uu____13731 = check_let_recs rec_env lbs2 in
                         (match uu____13731 with
                          | (lbs3,g_lbs) ->
                              let uu____13750 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___125_13773 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___125_13773.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___125_13773.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___126_13775 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___126_13775.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___126_13775.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___126_13775.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___126_13775.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____13750 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____13802 = tc_term env2 e21 in
                                   (match uu____13802 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____13819 =
                                            let uu____13820 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____13820 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____13819 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___127_13824 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___127_13824.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___127_13824.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___127_13824.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____13825 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____13825 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____13861 ->
                                                  (e, cres2, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  let cres3 =
                                                    let uu___128_13866 =
                                                      cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___128_13866.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___128_13866.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___128_13866.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____13869 -> failwith "Impossible"
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
          let uu____13899 =
            let uu____13904 =
              let uu____13905 = FStar_Syntax_Subst.compress t in
              uu____13905.FStar_Syntax_Syntax.n in
            let uu____13908 =
              let uu____13909 = FStar_Syntax_Subst.compress lbdef in
              uu____13909.FStar_Syntax_Syntax.n in
            (uu____13904, uu____13908) in
          match uu____13899 with
          | (FStar_Syntax_Syntax.Tm_arrow
             (formals,c),FStar_Syntax_Syntax.Tm_abs
             (actuals,uu____13915,uu____13916)) ->
              let actuals1 =
                let uu____13954 =
                  FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                FStar_TypeChecker_Util.maybe_add_implicit_binders uu____13954
                  actuals in
              (if (FStar_List.length formals) <> (FStar_List.length actuals1)
               then
                 (let actuals_msg =
                    let n1 = FStar_List.length actuals1 in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument was found"
                    else
                      (let uu____13975 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments were found"
                         uu____13975) in
                  let formals_msg =
                    let n1 = FStar_List.length formals in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument"
                    else
                      (let uu____13993 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments" uu____13993) in
                  let msg =
                    let uu____14001 = FStar_Syntax_Print.term_to_string lbtyp in
                    let uu____14002 =
                      FStar_Syntax_Print.lbname_to_string lbname in
                    FStar_Util.format4
                      "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                      uu____14001 uu____14002 formals_msg actuals_msg in
                  FStar_Exn.raise
                    (FStar_Errors.Error
                       (msg, (lbdef.FStar_Syntax_Syntax.pos))))
               else ();
               (let quals =
                  FStar_TypeChecker_Env.lookup_effect_quals env
                    (FStar_Syntax_Util.comp_effect_name c) in
                FStar_All.pipe_right quals
                  (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
          | uu____14009 ->
              let uu____14014 =
                let uu____14015 =
                  let uu____14020 =
                    let uu____14021 = FStar_Syntax_Print.term_to_string lbdef in
                    let uu____14022 = FStar_Syntax_Print.term_to_string lbtyp in
                    FStar_Util.format2
                      "Only function literals with arrow types can be defined recursively; got %s : %s"
                      uu____14021 uu____14022 in
                  (uu____14020, (lbtyp.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____14015 in
              FStar_Exn.raise uu____14014 in
        let uu____14023 =
          FStar_List.fold_left
            (fun uu____14049  ->
               fun lb  ->
                 match uu____14049 with
                 | (lbs1,env1) ->
                     let uu____14069 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____14069 with
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
                              (let uu____14089 =
                                 let uu____14096 =
                                   let uu____14097 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____14097 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___129_14108 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___129_14108.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___129_14108.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___129_14108.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___129_14108.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___129_14108.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___129_14108.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___129_14108.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___129_14108.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___129_14108.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___129_14108.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___129_14108.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___129_14108.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___129_14108.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___129_14108.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___129_14108.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___129_14108.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___129_14108.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___129_14108.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___129_14108.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___129_14108.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___129_14108.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___129_14108.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___129_14108.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___129_14108.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___129_14108.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___129_14108.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___129_14108.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___129_14108.FStar_TypeChecker_Env.identifier_info)
                                    }) t uu____14096 in
                               match uu____14089 with
                               | (t1,uu____14110,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____14114 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____14114);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____14116 =
                              termination_check_enabled
                                lb.FStar_Syntax_Syntax.lbname e t1 in
                            if uu____14116
                            then
                              let uu___130_14117 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___130_14117.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___130_14117.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___130_14117.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___130_14117.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___130_14117.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___130_14117.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___130_14117.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___130_14117.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___130_14117.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___130_14117.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___130_14117.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___130_14117.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___130_14117.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___130_14117.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___130_14117.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___130_14117.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___130_14117.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___130_14117.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___130_14117.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___130_14117.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___130_14117.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___130_14117.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___130_14117.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___130_14117.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___130_14117.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___130_14117.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___130_14117.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___130_14117.FStar_TypeChecker_Env.identifier_info)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1) in
                          let lb1 =
                            let uu___131_14134 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___131_14134.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___131_14134.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____14023 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lbs  ->
      let uu____14157 =
        let uu____14166 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____14195 =
                     let uu____14196 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____14196.FStar_Syntax_Syntax.n in
                   match uu____14195 with
                   | FStar_Syntax_Syntax.Tm_abs uu____14199 -> ()
                   | uu____14216 ->
                       let uu____14217 =
                         let uu____14218 =
                           let uu____14223 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____14223) in
                         FStar_Errors.Error uu____14218 in
                       FStar_Exn.raise uu____14217);
                  (let uu____14224 =
                     let uu____14231 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____14231
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____14224 with
                   | (e,c,g) ->
                       ((let uu____14240 =
                           let uu____14241 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____14241 in
                         if uu____14240
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
        FStar_All.pipe_right uu____14166 FStar_List.unzip in
      match uu____14157 with
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
        let uu____14290 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____14290 with
        | (env1,uu____14308) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____14316 = check_lbtyp top_level env lb in
            (match uu____14316 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Exn.raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____14360 =
                     tc_maybe_toplevel_term
                       (let uu___132_14369 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___132_14369.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___132_14369.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___132_14369.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___132_14369.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___132_14369.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___132_14369.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___132_14369.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___132_14369.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___132_14369.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___132_14369.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___132_14369.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___132_14369.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___132_14369.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___132_14369.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___132_14369.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___132_14369.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___132_14369.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___132_14369.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___132_14369.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.failhard =
                            (uu___132_14369.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.type_of =
                            (uu___132_14369.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___132_14369.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___132_14369.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___132_14369.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___132_14369.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___132_14369.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___132_14369.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___132_14369.FStar_TypeChecker_Env.identifier_info)
                        }) e11 in
                   match uu____14360 with
                   | (e12,c1,g1) ->
                       let uu____14383 =
                         let uu____14388 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____14392  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____14388 e12 c1 wf_annot in
                       (match uu____14383 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____14407 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____14407
                              then
                                let uu____14408 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____14409 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____14410 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____14408 uu____14409 uu____14410
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
        | uu____14454 ->
            let uu____14455 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____14455 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____14504 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____14504)
                 else
                   (let uu____14512 = FStar_Syntax_Util.type_u () in
                    match uu____14512 with
                    | (k,uu____14532) ->
                        let uu____14533 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____14533 with
                         | (t2,uu____14555,g) ->
                             ((let uu____14558 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____14558
                               then
                                 let uu____14559 =
                                   let uu____14560 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____14560 in
                                 let uu____14561 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____14559 uu____14561
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____14564 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____14564))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun uu____14572  ->
      match uu____14572 with
      | (x,imp) ->
          let uu____14591 = FStar_Syntax_Util.type_u () in
          (match uu____14591 with
           | (tu,u) ->
               ((let uu____14611 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____14611
                 then
                   let uu____14612 = FStar_Syntax_Print.bv_to_string x in
                   let uu____14613 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____14614 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____14612 uu____14613 uu____14614
                 else ());
                (let uu____14616 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____14616 with
                 | (t,uu____14636,g) ->
                     let x1 =
                       ((let uu___133_14644 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___133_14644.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___133_14644.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____14646 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____14646
                       then
                         let uu____14647 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1) in
                         let uu____14648 =
                           FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____14647 uu____14648
                       else ());
                      (let uu____14650 = push_binding env x1 in
                       (x1, uu____14650, g, u))))))
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
            let uu____14740 = tc_binder env1 b in
            (match uu____14740 with
             | (b1,env',g,u) ->
                 let uu____14781 = aux env' bs2 in
                 (match uu____14781 with
                  | (bs3,env'1,g',us) ->
                      let uu____14834 =
                        let uu____14835 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____14835 in
                      ((b1 :: bs3), env'1, uu____14834, (u :: us)))) in
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
          (fun uu____14920  ->
             fun uu____14921  ->
               match (uu____14920, uu____14921) with
               | ((t,imp),(args1,g)) ->
                   let uu____14990 = tc_term env1 t in
                   (match uu____14990 with
                    | (t1,uu____15008,g') ->
                        let uu____15010 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____15010))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____15052  ->
             match uu____15052 with
             | (pats1,g) ->
                 let uu____15077 = tc_args env p in
                 (match uu____15077 with
                  | (args,g') ->
                      let uu____15090 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____15090))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let uu____15103 = tc_maybe_toplevel_term env e in
      match uu____15103 with
      | (e1,c,g) ->
          let uu____15119 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____15119
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____15132 =
               let uu____15137 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____15137
               then
                 let uu____15142 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____15142, false)
               else
                 (let uu____15144 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____15144, true)) in
             match uu____15132 with
             | (target_comp,allow_ghost) ->
                 let uu____15153 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____15153 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____15163 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____15163)
                  | uu____15164 ->
                      if allow_ghost
                      then
                        let uu____15173 =
                          let uu____15174 =
                            let uu____15179 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____15179, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____15174 in
                        FStar_Exn.raise uu____15173
                      else
                        (let uu____15187 =
                           let uu____15188 =
                             let uu____15193 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____15193, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____15188 in
                         FStar_Exn.raise uu____15187)))
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
      let uu____15212 = tc_tot_or_gtot_term env t in
      match uu____15212 with
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
      (let uu____15242 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____15242
       then
         let uu____15243 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____15243
       else ());
      (let env1 =
         let uu___134_15246 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___134_15246.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___134_15246.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___134_15246.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___134_15246.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___134_15246.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___134_15246.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___134_15246.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___134_15246.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___134_15246.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___134_15246.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___134_15246.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___134_15246.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___134_15246.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___134_15246.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___134_15246.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___134_15246.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___134_15246.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___134_15246.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.failhard =
             (uu___134_15246.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.type_of =
             (uu___134_15246.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___134_15246.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___134_15246.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___134_15246.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___134_15246.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___134_15246.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___134_15246.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___134_15246.FStar_TypeChecker_Env.identifier_info)
         } in
       let uu____15251 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____15284) ->
             let uu____15285 =
               let uu____15286 =
                 let uu____15291 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____15291) in
               FStar_Errors.Error uu____15286 in
             FStar_Exn.raise uu____15285 in
       match uu____15251 with
       | (t,c,g) ->
           let uu____15307 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____15307
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____15317 =
                let uu____15318 =
                  let uu____15323 =
                    let uu____15324 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____15324 in
                  let uu____15325 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____15323, uu____15325) in
                FStar_Errors.Error uu____15318 in
              FStar_Exn.raise uu____15317))
let level_of_type_fail:
  'Auu____15340 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____15340
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____15353 =
          let uu____15354 =
            let uu____15359 =
              let uu____15360 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format2
                "Expected a term of type 'Type'; got %s : %s" uu____15360 t in
            let uu____15361 = FStar_TypeChecker_Env.get_range env in
            (uu____15359, uu____15361) in
          FStar_Errors.Error uu____15354 in
        FStar_Exn.raise uu____15353
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____15381 =
            let uu____15382 = FStar_Syntax_Util.unrefine t1 in
            uu____15382.FStar_Syntax_Syntax.n in
          match uu____15381 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____15386 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____15389 = FStar_Syntax_Util.type_u () in
                 match uu____15389 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___137_15397 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___137_15397.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___137_15397.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___137_15397.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___137_15397.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___137_15397.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___137_15397.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___137_15397.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___137_15397.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___137_15397.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___137_15397.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___137_15397.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___137_15397.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___137_15397.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___137_15397.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___137_15397.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___137_15397.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___137_15397.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___137_15397.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___137_15397.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___137_15397.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.type_of =
                           (uu___137_15397.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___137_15397.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___137_15397.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___137_15397.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___137_15397.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___137_15397.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___137_15397.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___137_15397.FStar_TypeChecker_Env.identifier_info)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____15401 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____15401
                       | uu____15402 ->
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
      let uu____15413 =
        let uu____15414 = FStar_Syntax_Subst.compress e in
        uu____15414.FStar_Syntax_Syntax.n in
      match uu____15413 with
      | FStar_Syntax_Syntax.Tm_bvar uu____15419 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____15424 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____15451 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____15467) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____15490,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____15517) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____15524 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____15524 with | ((uu____15535,t),uu____15537) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____15542,(FStar_Util.Inl t,uu____15544),uu____15545) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____15592,(FStar_Util.Inr c,uu____15594),uu____15595) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____15645;
             FStar_Syntax_Syntax.vars = uu____15646;_},us)
          ->
          let uu____15652 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____15652 with
           | ((us',t),uu____15665) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____15671 =
                     let uu____15672 =
                       let uu____15677 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____15677) in
                     FStar_Errors.Error uu____15672 in
                   FStar_Exn.raise uu____15671)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____15693 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____15694 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____15704) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____15727 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____15727 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____15747  ->
                      match uu____15747 with
                      | (b,uu____15753) ->
                          let uu____15754 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____15754) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____15759 = universe_of_aux env res in
                 level_of_type env res uu____15759 in
               let u_c =
                 let uu____15761 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____15761 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____15765 = universe_of_aux env trepr in
                     level_of_type env trepr uu____15765 in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____15858 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____15873 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____15912 ->
                let uu____15913 = universe_of_aux env hd3 in
                (uu____15913, args1)
            | FStar_Syntax_Syntax.Tm_name uu____15926 ->
                let uu____15927 = universe_of_aux env hd3 in
                (uu____15927, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____15940 ->
                let uu____15957 = universe_of_aux env hd3 in
                (uu____15957, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____15970 ->
                let uu____15977 = universe_of_aux env hd3 in
                (uu____15977, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____15990 ->
                let uu____16017 = universe_of_aux env hd3 in
                (uu____16017, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____16030 ->
                let uu____16037 = universe_of_aux env hd3 in
                (uu____16037, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____16050 ->
                let uu____16051 = universe_of_aux env hd3 in
                (uu____16051, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____16064 ->
                let uu____16077 = universe_of_aux env hd3 in
                (uu____16077, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____16090 ->
                let uu____16097 = universe_of_aux env hd3 in
                (uu____16097, args1)
            | FStar_Syntax_Syntax.Tm_type uu____16110 ->
                let uu____16111 = universe_of_aux env hd3 in
                (uu____16111, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____16124,hd4::uu____16126) ->
                let uu____16191 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____16191 with
                 | (uu____16206,uu____16207,hd5) ->
                     let uu____16225 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____16225 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____16276 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____16278 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____16278 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____16329 ->
                let uu____16330 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____16330 with
                 | (env1,uu____16352) ->
                     let env2 =
                       let uu___138_16358 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___138_16358.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___138_16358.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___138_16358.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___138_16358.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___138_16358.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___138_16358.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___138_16358.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___138_16358.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___138_16358.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___138_16358.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___138_16358.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___138_16358.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___138_16358.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___138_16358.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___138_16358.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___138_16358.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___138_16358.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___138_16358.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.failhard =
                           (uu___138_16358.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.type_of =
                           (uu___138_16358.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___138_16358.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___138_16358.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___138_16358.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___138_16358.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___138_16358.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___138_16358.FStar_TypeChecker_Env.identifier_info)
                       } in
                     ((let uu____16360 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____16360
                       then
                         let uu____16361 =
                           let uu____16362 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____16362 in
                         let uu____16363 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____16361 uu____16363
                       else ());
                      (let uu____16365 = tc_term env2 hd3 in
                       match uu____16365 with
                       | (uu____16386,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____16387;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____16389;
                                        FStar_Syntax_Syntax.comp =
                                          uu____16390;_},g)
                           ->
                           ((let uu____16401 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____16401
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____16412 = type_of_head true hd1 args in
          (match uu____16412 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____16452 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____16452 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____16496 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____16496)))
      | FStar_Syntax_Syntax.Tm_match (uu____16499,hd1::uu____16501) ->
          let uu____16566 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____16566 with
           | (uu____16569,uu____16570,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____16588,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____16633 = universe_of_aux env e in
      level_of_type env e uu____16633
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tps  ->
      let uu____16654 = tc_binders env tps in
      match uu____16654 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))