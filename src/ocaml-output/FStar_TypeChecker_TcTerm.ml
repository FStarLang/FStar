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
           let uu____41 =
             let uu____42 =
               let uu____43 = FStar_Syntax_Syntax.as_arg v1 in
               let uu____44 =
                 let uu____46 = FStar_Syntax_Syntax.as_arg tl1 in [uu____46] in
               uu____43 :: uu____44 in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____42 in
           uu____41
             (FStar_Pervasives_Native.Some
                (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r) vs
      FStar_Syntax_Util.lex_top
let is_eq:
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___84_55  ->
    match uu___84_55 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____57 -> false
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
            | uu____112 ->
                let t1 = if try_norm then norm env t else t in
                let fvs' = FStar_Syntax_Free.names t1 in
                let uu____118 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs in
                (match uu____118 with
                 | FStar_Pervasives_Native.None  -> t1
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____127 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____129 =
                                  FStar_Syntax_Print.bv_to_string x in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____129
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____131 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____132 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1 in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____131 uu____132 in
                          let uu____133 =
                            let uu____134 =
                              let uu____137 =
                                FStar_TypeChecker_Env.get_range env in
                              (msg, uu____137) in
                            FStar_Errors.Error uu____134 in
                          raise uu____133 in
                        let s =
                          let uu____139 =
                            let uu____140 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____140 in
                          FStar_TypeChecker_Util.new_uvar env uu____139 in
                        let uu____145 =
                          FStar_TypeChecker_Rel.try_teq true env t1 s in
                        match uu____145 with
                        | FStar_Pervasives_Native.Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____149 -> fail ())) in
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
        let uu____186 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____186
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
      let uu___91_202 = lc in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___91_202.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___91_202.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____205  ->
             let uu____206 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Util.set_result_typ uu____206 t)
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
            let uu____251 =
              let uu____252 = FStar_Syntax_Subst.compress t in
              uu____252.FStar_Syntax_Syntax.n in
            match uu____251 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____255,c) ->
                let uu____267 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c) in
                if uu____267
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c) in
                  let uu____269 =
                    let uu____270 = FStar_Syntax_Subst.compress t1 in
                    uu____270.FStar_Syntax_Syntax.n in
                  (match uu____269 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____274 -> false
                   | uu____275 -> true)
                else false
            | uu____277 -> true in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____280 =
                  let uu____283 =
                    (let uu____286 = should_return t in
                     Prims.op_Negation uu____286) ||
                      (let uu____288 =
                         FStar_TypeChecker_Env.should_verify env in
                       Prims.op_Negation uu____288) in
                  if uu____283
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e in
                FStar_Syntax_Util.lcomp_of_comp uu____280
            | FStar_Util.Inr lc -> lc in
          let t = lc.FStar_Syntax_Syntax.res_typ in
          let uu____296 =
            let uu____300 = FStar_TypeChecker_Env.expected_typ env in
            match uu____300 with
            | FStar_Pervasives_Native.None  ->
                let uu____305 = memo_tk e t in (uu____305, lc, guard)
            | FStar_Pervasives_Native.Some t' ->
                ((let uu____308 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High in
                  if uu____308
                  then
                    let uu____309 = FStar_Syntax_Print.term_to_string t in
                    let uu____310 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____309
                      uu____310
                  else ());
                 (let uu____312 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t' in
                  match uu____312 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____323 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____323 with
                       | (e2,g) ->
                           ((let uu____332 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____332
                             then
                               let uu____333 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____334 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____335 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____336 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____333 uu____334 uu____335 uu____336
                             else ());
                            (let msg =
                               let uu____342 =
                                 FStar_TypeChecker_Rel.is_trivial g in
                               if uu____342
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_39  ->
                                      FStar_Pervasives_Native.Some _0_39)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             let uu____357 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1 in
                             match uu____357 with
                             | (lc2,g2) ->
                                 let uu____365 = memo_tk e2 t' in
                                 (uu____365, (set_lcomp_result lc2 t'), g2)))))) in
          match uu____296 with
          | (e1,lc1,g) ->
              ((let uu____373 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low in
                if uu____373
                then
                  let uu____374 = FStar_Syntax_Print.lcomp_to_string lc1 in
                  FStar_Util.print1 "Return comp type is %s\n" uu____374
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
        let uu____394 = FStar_TypeChecker_Env.expected_typ env in
        match uu____394 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____400 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____400 with
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
      fun uu____425  ->
        match uu____425 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____445 = FStar_Syntax_Util.is_pure_comp c1 in
              if uu____445
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____447 = FStar_Syntax_Util.is_pure_or_ghost_comp c1 in
                 if uu____447
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp") in
            let uu____449 =
              match copt with
              | FStar_Pervasives_Native.Some uu____456 -> (copt, c)
              | FStar_Pervasives_Native.None  ->
                  let uu____458 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____460 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____460)) in
                  if uu____458
                  then
                    let uu____464 =
                      let uu____466 =
                        FStar_Syntax_Util.ml_comp
                          (FStar_Syntax_Util.comp_result c)
                          e.FStar_Syntax_Syntax.pos in
                      FStar_Pervasives_Native.Some uu____466 in
                    (uu____464, c)
                  else
                    (let uu____469 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____469
                     then
                       let uu____473 = tot_or_gtot c in
                       (FStar_Pervasives_Native.None, uu____473)
                     else
                       (let uu____476 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c in
                        if uu____476
                        then
                          let uu____480 =
                            let uu____482 = tot_or_gtot c in
                            FStar_Pervasives_Native.Some uu____482 in
                          (uu____480, c)
                        else (FStar_Pervasives_Native.None, c))) in
            (match uu____449 with
             | (expected_c_opt,c1) ->
                 let c2 = norm_c env c1 in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2, FStar_TypeChecker_Rel.trivial_guard)
                  | FStar_Pervasives_Native.Some expected_c ->
                      let uu____498 =
                        FStar_TypeChecker_Util.check_comp env e c2 expected_c in
                      (match uu____498 with
                       | (e1,uu____506,g) ->
                           let g1 =
                             let uu____509 =
                               FStar_TypeChecker_Env.get_range env in
                             FStar_TypeChecker_Util.label_guard uu____509
                               "could not prove post-condition" g in
                           ((let uu____511 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Low in
                             if uu____511
                             then
                               let uu____512 =
                                 FStar_Range.string_of_range
                                   e1.FStar_Syntax_Syntax.pos in
                               let uu____513 =
                                 FStar_TypeChecker_Rel.guard_to_string env g1 in
                               FStar_Util.print2
                                 "(%s) DONE check_expected_effect; guard is: %s\n"
                                 uu____512 uu____513
                             else ());
                            (let e2 =
                               FStar_TypeChecker_Util.maybe_lift env e1
                                 (FStar_Syntax_Util.comp_effect_name c2)
                                 (FStar_Syntax_Util.comp_effect_name
                                    expected_c)
                                 (FStar_Syntax_Util.comp_result c2) in
                             (e2, expected_c, g1))))))
let no_logical_guard env uu____539 =
  match uu____539 with
  | (te,kt,f) ->
      let uu____546 = FStar_TypeChecker_Rel.guard_form f in
      (match uu____546 with
       | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
       | FStar_TypeChecker_Common.NonTrivial f1 ->
           let uu____551 =
             let uu____552 =
               let uu____555 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1 in
               let uu____556 = FStar_TypeChecker_Env.get_range env in
               (uu____555, uu____556) in
             FStar_Errors.Error uu____552 in
           raise uu____551)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____564 = FStar_TypeChecker_Env.expected_typ env in
    match uu____564 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None"
    | FStar_Pervasives_Native.Some t ->
        let uu____567 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____567
let check_smt_pat env t bs c =
  let uu____608 = FStar_Syntax_Util.is_smt_lemma t in
  if uu____608
  then
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp
        { FStar_Syntax_Syntax.comp_univs = uu____609;
          FStar_Syntax_Syntax.effect_name = uu____610;
          FStar_Syntax_Syntax.result_typ = uu____611;
          FStar_Syntax_Syntax.effect_args = _pre::_post::(pats,uu____615)::[];
          FStar_Syntax_Syntax.flags = uu____616;_}
        ->
        let pat_vars =
          let uu____650 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta] env pats in
          FStar_Syntax_Free.names uu____650 in
        let uu____651 =
          FStar_All.pipe_right bs
            (FStar_Util.find_opt
               (fun uu____667  ->
                  match uu____667 with
                  | (b,uu____671) ->
                      let uu____672 = FStar_Util.set_mem b pat_vars in
                      Prims.op_Negation uu____672)) in
        (match uu____651 with
         | FStar_Pervasives_Native.None  -> ()
         | FStar_Pervasives_Native.Some (x,uu____676) ->
             let uu____679 =
               let uu____680 = FStar_Syntax_Print.bv_to_string x in
               FStar_Util.format1
                 "Pattern misses at least one bound variable: %s" uu____680 in
             FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____679)
    | uu____681 -> failwith "Impossible"
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
        let uu____705 =
          let uu____706 = FStar_TypeChecker_Env.should_verify env in
          Prims.op_Negation uu____706 in
        if uu____705
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env in
               let env1 =
                 let uu___92_724 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___92_724.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___92_724.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___92_724.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___92_724.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___92_724.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___92_724.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___92_724.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___92_724.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___92_724.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___92_724.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___92_724.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___92_724.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___92_724.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___92_724.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___92_724.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___92_724.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___92_724.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___92_724.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___92_724.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___92_724.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___92_724.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___92_724.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___92_724.FStar_TypeChecker_Env.qname_and_index);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___92_724.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth =
                     (uu___92_724.FStar_TypeChecker_Env.synth);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___92_724.FStar_TypeChecker_Env.is_native_tactic)
                 } in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Parser_Const.precedes_lid in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____752  ->
                           match uu____752 with
                           | (b,uu____757) ->
                               let t =
                                 let uu____759 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort in
                                 FStar_TypeChecker_Normalize.unfold_whnf env1
                                   uu____759 in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type uu____761 -> []
                                | FStar_Syntax_Syntax.Tm_arrow uu____762 ->
                                    []
                                | uu____770 ->
                                    let uu____771 =
                                      FStar_Syntax_Syntax.bv_to_name b in
                                    [uu____771]))) in
                 let as_lex_list dec =
                   let uu____776 = FStar_Syntax_Util.head_and_args dec in
                   match uu____776 with
                   | (head1,uu____787) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.lexcons_lid
                            -> dec
                        | uu____803 -> mk_lex_list [dec]) in
                 let cflags = FStar_Syntax_Util.comp_flags c in
                 let uu____806 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___85_812  ->
                           match uu___85_812 with
                           | FStar_Syntax_Syntax.DECREASES uu____813 -> true
                           | uu____816 -> false)) in
                 match uu____806 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.DECREASES dec) -> as_lex_list dec
                 | uu____820 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions in
                     (match xs with
                      | x::[] -> x
                      | uu____826 -> mk_lex_list xs) in
               let previous_dec = decreases_clause actuals expected_c in
               let guard_one_letrec uu____838 =
                 match uu____838 with
                 | (l,t) ->
                     let uu____847 =
                       let uu____848 = FStar_Syntax_Subst.compress t in
                       uu____848.FStar_Syntax_Syntax.n in
                     (match uu____847 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____886  ->
                                    match uu____886 with
                                    | (x,imp) ->
                                        let uu____893 =
                                          FStar_Syntax_Syntax.is_null_bv x in
                                        if uu____893
                                        then
                                          let uu____896 =
                                            let uu____897 =
                                              let uu____899 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x in
                                              FStar_Pervasives_Native.Some
                                                uu____899 in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____897
                                              x.FStar_Syntax_Syntax.sort in
                                          (uu____896, imp)
                                        else (x, imp))) in
                          let uu____901 =
                            FStar_Syntax_Subst.open_comp formals1 c in
                          (match uu____901 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1 in
                               let precedes1 =
                                 let uu____914 =
                                   let uu____915 =
                                     let uu____916 =
                                       FStar_Syntax_Syntax.as_arg dec in
                                     let uu____917 =
                                       let uu____919 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec in
                                       [uu____919] in
                                     uu____916 :: uu____917 in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____915 in
                                 uu____914 FStar_Pervasives_Native.None r in
                               let uu____924 = FStar_Util.prefix formals2 in
                               (match uu____924 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___93_950 = last1 in
                                      let uu____951 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1 in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___93_950.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___93_950.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____951
                                      } in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)] in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1 in
                                    ((let uu____968 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low in
                                      if uu____968
                                      then
                                        let uu____969 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l in
                                        let uu____970 =
                                          FStar_Syntax_Print.term_to_string t in
                                        let uu____971 =
                                          FStar_Syntax_Print.term_to_string
                                            t' in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____969 uu____970 uu____971
                                      else ());
                                     (l, t'))))
                      | uu____975 ->
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
        (let uu___94_1262 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___94_1262.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___94_1262.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___94_1262.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___94_1262.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___94_1262.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___94_1262.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___94_1262.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___94_1262.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___94_1262.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___94_1262.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___94_1262.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___94_1262.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___94_1262.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___94_1262.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___94_1262.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___94_1262.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___94_1262.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___94_1262.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___94_1262.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___94_1262.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___94_1262.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___94_1262.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___94_1262.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___94_1262.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___94_1262.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___94_1262.FStar_TypeChecker_Env.is_native_tactic)
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
      (let uu____1271 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1271
       then
         let uu____1272 =
           let uu____1273 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1273 in
         let uu____1274 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1272 uu____1274
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1280 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1298 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1303 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1314 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1315 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1316 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1317 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1318 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1328 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1336 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1341 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1347 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1347 with
            | (e2,c,g) ->
                let g1 =
                  let uu___95_1358 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___95_1358.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___95_1358.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___95_1358.FStar_TypeChecker_Env.implicits)
                  } in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1371 = FStar_Syntax_Util.type_u () in
           (match uu____1371 with
            | (t,u) ->
                let uu____1379 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1379 with
                 | (e2,c,g) ->
                     let uu____1389 =
                       let uu____1398 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____1398 with
                       | (env2,uu____1411) -> tc_pats env2 pats in
                     (match uu____1389 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___96_1432 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___96_1432.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___96_1432.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___96_1432.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____1433 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              (FStar_Pervasives_Native.Some
                                 (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____1440 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____1433, c, uu____1440))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1448 =
             let uu____1449 = FStar_Syntax_Subst.compress e1 in
             uu____1449.FStar_Syntax_Syntax.n in
           (match uu____1448 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1455,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1457;
                               FStar_Syntax_Syntax.lbtyp = uu____1458;
                               FStar_Syntax_Syntax.lbeff = uu____1459;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____1477 =
                  let uu____1481 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_TypeChecker_Common.t_unit in
                  tc_term uu____1481 e11 in
                (match uu____1477 with
                 | (e12,c1,g1) ->
                     let uu____1488 = tc_term env1 e2 in
                     (match uu____1488 with
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
                            let uu____1505 =
                              let uu____1508 =
                                let uu____1509 =
                                  let uu____1517 =
                                    let uu____1521 =
                                      let uu____1523 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_TypeChecker_Common.t_unit,
                                            e13) in
                                      [uu____1523] in
                                    (false, uu____1521) in
                                  (uu____1517, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____1509 in
                              FStar_Syntax_Syntax.mk uu____1508 in
                            uu____1505
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
                          let uu____1549 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____1549)))
            | uu____1552 ->
                let uu____1553 = tc_term env1 e1 in
                (match uu____1553 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____1573) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____1588 = tc_term env1 e1 in
           (match uu____1588 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    (FStar_Pervasives_Native.Some
                       ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____1610) ->
           let uu____1646 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____1646 with
            | (env0,uu____1654) ->
                let uu____1657 = tc_comp env0 expected_c in
                (match uu____1657 with
                 | (expected_c1,uu____1665,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____1670 =
                       let uu____1674 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____1674 e1 in
                     (match uu____1670 with
                      | (e2,c',g') ->
                          let uu____1681 =
                            let uu____1685 =
                              let uu____1688 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____1688) in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____1685 in
                          (match uu____1681 with
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
                                 let uu____1735 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____1735 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (FStar_TypeChecker_Common.mk_by_tactic
                                          tactic) in
                               let uu____1740 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____1740 with
                                | (e5,c,f2) ->
                                    let uu____1750 =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, uu____1750))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____1754) ->
           let uu____1790 = FStar_Syntax_Util.type_u () in
           (match uu____1790 with
            | (k,u) ->
                let uu____1798 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____1798 with
                 | (t1,uu____1806,f) ->
                     let uu____1808 =
                       let uu____1812 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____1812 e1 in
                     (match uu____1808 with
                      | (e2,c,g) ->
                          let uu____1819 =
                            let uu____1822 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____1826  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____1822 e2 c f in
                          (match uu____1819 with
                           | (c1,f1) ->
                               let uu____1832 =
                                 let uu____1836 =
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
                                 comp_check_expected_typ env1 uu____1836 c1 in
                               (match uu____1832 with
                                | (e3,c2,f2) ->
                                    let uu____1868 =
                                      let uu____1869 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____1869 in
                                    (e3, c2, uu____1868))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____1870;
              FStar_Syntax_Syntax.pos = uu____1871;
              FStar_Syntax_Syntax.vars = uu____1872;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____1916 = FStar_Syntax_Util.head_and_args top in
           (match uu____1916 with
            | (unary_op,uu____1930) ->
                let head1 =
                  let uu____1948 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____1948 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____1984);
              FStar_Syntax_Syntax.tk = uu____1985;
              FStar_Syntax_Syntax.pos = uu____1986;
              FStar_Syntax_Syntax.vars = uu____1987;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2031 = FStar_Syntax_Util.head_and_args top in
           (match uu____2031 with
            | (unary_op,uu____2045) ->
                let head1 =
                  let uu____2063 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2063 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____2099;
              FStar_Syntax_Syntax.pos = uu____2100;
              FStar_Syntax_Syntax.vars = uu____2101;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____2127 =
               let uu____2131 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____2131 with | (env0,uu____2139) -> tc_term env0 e1 in
             match uu____2127 with
             | (e2,c,g) ->
                 let uu____2148 = FStar_Syntax_Util.head_and_args top in
                 (match uu____2148 with
                  | (reify_op,uu____2162) ->
                      let u_c =
                        let uu____2178 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____2178 with
                        | (uu____2182,c',uu____2184) ->
                            let uu____2185 =
                              let uu____2186 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____2186.FStar_Syntax_Syntax.n in
                            (match uu____2185 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____2190 ->
                                 let uu____2191 = FStar_Syntax_Util.type_u () in
                                 (match uu____2191 with
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
                                            let uu____2200 =
                                              let uu____2201 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____2202 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____2203 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____2201 uu____2202
                                                uu____2203 in
                                            failwith uu____2200);
                                       u))) in
                      let repr =
                        let uu____2205 = c.FStar_Syntax_Syntax.comp () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____2205 u_c in
                      let e3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (reify_op, [(e2, aqual)]))
                          (FStar_Pervasives_Native.Some
                             (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____2223 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____2223
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____2224 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____2224 with
                       | (e4,c2,g') ->
                           let uu____2234 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____2234)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____2236;
              FStar_Syntax_Syntax.pos = uu____2237;
              FStar_Syntax_Syntax.vars = uu____2238;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____2270 =
               let uu____2271 =
                 let uu____2272 =
                   let uu____2275 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____2275, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____2272 in
               raise uu____2271 in
             let uu____2279 = FStar_Syntax_Util.head_and_args top in
             match uu____2279 with
             | (reflect_op,uu____2293) ->
                 let uu____2308 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____2308 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____2326 =
                        let uu____2327 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____2327 in
                      if uu____2326
                      then no_reflect ()
                      else
                        (let uu____2333 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____2333 with
                         | (env_no_ex,topt) ->
                             let uu____2344 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____2359 =
                                   let uu____2362 =
                                     let uu____2363 =
                                       let uu____2373 =
                                         let uu____2375 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____2376 =
                                           let uu____2378 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____2378] in
                                         uu____2375 :: uu____2376 in
                                       (repr, uu____2373) in
                                     FStar_Syntax_Syntax.Tm_app uu____2363 in
                                   FStar_Syntax_Syntax.mk uu____2362 in
                                 uu____2359 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos in
                               let uu____2388 =
                                 let uu____2392 =
                                   let uu____2393 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____2393
                                     FStar_Pervasives_Native.fst in
                                 tc_tot_or_gtot_term uu____2392 t in
                               match uu____2388 with
                               | (t1,uu____2410,g) ->
                                   let uu____2412 =
                                     let uu____2413 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____2413.FStar_Syntax_Syntax.n in
                                   (match uu____2412 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____2424,(res,uu____2426)::
                                         (wp,uu____2428)::[])
                                        -> (t1, res, wp, g)
                                    | uu____2462 -> failwith "Impossible") in
                             (match uu____2344 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____2486 =
                                    let uu____2489 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____2489 with
                                    | (e2,c,g) ->
                                        ((let uu____2499 =
                                            let uu____2500 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____2500 in
                                          if uu____2499
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____2506 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____2506 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____2511 =
                                                  let uu____2515 =
                                                    let uu____2518 =
                                                      let uu____2519 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____2520 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____2519 uu____2520 in
                                                    (uu____2518,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____2515] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____2511);
                                               (let uu____2525 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____2525)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____2527 =
                                                let uu____2528 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____2528 in
                                              (e2, uu____2527))) in
                                  (match uu____2486 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____2535 =
                                           let uu____2536 =
                                             let uu____2537 =
                                               let uu____2538 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____2538] in
                                             let uu____2539 =
                                               let uu____2545 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____2545] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____2537;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____2539;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____2536 in
                                         FStar_All.pipe_right uu____2535
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           (FStar_Pervasives_Native.Some
                                              (res_typ.FStar_Syntax_Syntax.n))
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____2562 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____2562 with
                                        | (e4,c1,g') ->
                                            let uu____2572 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____2572))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           tc_synth env1 args top.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____2607 =
               let uu____2608 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____2608 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____2607 instantiate_both in
           ((let uu____2617 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____2617
             then
               let uu____2618 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____2619 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____2618
                 uu____2619
             else ());
            (let isquote =
               match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.quote_lid
                   -> true
               | uu____2623 -> false in
             let uu____2624 = tc_term (no_inst env2) head1 in
             match uu____2624 with
             | (head2,chead,g_head) ->
                 let uu____2634 =
                   let uu____2638 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____2638
                   then
                     let uu____2642 =
                       let uu____2646 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____2646 in
                     match uu____2642 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____2655 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____2657 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c in
                                 Prims.op_Negation uu____2657))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                           if uu____2655
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c in
                         (e1, c1, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2 in
                      let uu____2662 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env3 head2 chead g_head args
                        uu____2662) in
                 (match uu____2634 with
                  | (e1,c,g) ->
                      ((let uu____2671 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____2671
                        then
                          let uu____2672 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____2672
                        else ());
                       (let uu____2674 = comp_check_expected_typ env0 e1 c in
                        match uu____2674 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____2685 =
                                let uu____2686 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____2686.FStar_Syntax_Syntax.n in
                              match uu____2685 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2690) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___97_2730 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___97_2730.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___97_2730.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___97_2730.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2759 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____2761 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____2761 in
                            ((let uu____2763 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____2763
                              then
                                let uu____2764 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____2765 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____2764 uu____2765
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2793 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2793 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____2805 = tc_term env12 e1 in
                (match uu____2805 with
                 | (e11,c1,g1) ->
                     let uu____2815 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____2821 = FStar_Syntax_Util.type_u () in
                           (match uu____2821 with
                            | (k,uu____2827) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____2829 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____2829, res_t)) in
                     (match uu____2815 with
                      | (env_branches,res_t) ->
                          ((let uu____2836 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____2836
                            then
                              let uu____2837 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____2837
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____2886 =
                              let uu____2889 =
                                FStar_List.fold_right
                                  (fun uu____2917  ->
                                     fun uu____2918  ->
                                       match (uu____2917, uu____2918) with
                                       | ((uu____2950,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____2983 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____2983))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____2889 with
                              | (cases,g) ->
                                  let uu____3004 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____3004, g) in
                            match uu____2886 with
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
                                           (fun uu____3065  ->
                                              match uu____3065 with
                                              | ((pat,wopt,br),uu____3081,lc,uu____3083)
                                                  ->
                                                  let uu____3090 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____3090))) in
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
                                  let uu____3138 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____3138
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____3145 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____3145 in
                                     let lb =
                                       let uu____3149 =
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
                                           uu____3149;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____3153 =
                                         let uu____3156 =
                                           let uu____3157 =
                                             let uu____3165 =
                                               let uu____3166 =
                                                 let uu____3167 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____3167] in
                                               FStar_Syntax_Subst.close
                                                 uu____3166 e_match in
                                             ((false, [lb]), uu____3165) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____3157 in
                                         FStar_Syntax_Syntax.mk uu____3156 in
                                       uu____3153
                                         (FStar_Pervasives_Native.Some
                                            ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____3181 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____3181
                                  then
                                    let uu____3182 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____3183 =
                                      let uu____3184 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____3184 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____3182 uu____3183
                                  else ());
                                 (let uu____3186 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____3186))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3189;
                FStar_Syntax_Syntax.lbunivs = uu____3190;
                FStar_Syntax_Syntax.lbtyp = uu____3191;
                FStar_Syntax_Syntax.lbeff = uu____3192;
                FStar_Syntax_Syntax.lbdef = uu____3193;_}::[]),uu____3194)
           ->
           ((let uu____3209 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3209
             then
               let uu____3210 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3210
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____3212),uu____3213) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3223;
                FStar_Syntax_Syntax.lbunivs = uu____3224;
                FStar_Syntax_Syntax.lbtyp = uu____3225;
                FStar_Syntax_Syntax.lbeff = uu____3226;
                FStar_Syntax_Syntax.lbdef = uu____3227;_}::uu____3228),uu____3229)
           ->
           ((let uu____3245 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3245
             then
               let uu____3246 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3246
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____3248),uu____3249) ->
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
        let uu____3267 =
          match args with
          | (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, FStar_Pervasives_Native.None, rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____3328))::(tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
             uu____3371))::(uu____3372,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____3373))::
              (tau,FStar_Pervasives_Native.None )::rest ->
              (tau, (FStar_Pervasives_Native.Some a), rest)
          | uu____3425 ->
              raise
                (FStar_Errors.Error ("synth_by_tactic: bad application", rng)) in
        match uu____3267 with
        | (tau,atyp,rest) ->
            let typ =
              match atyp with
              | FStar_Pervasives_Native.Some t -> t
              | FStar_Pervasives_Native.None  ->
                  let uu____3485 = FStar_TypeChecker_Env.expected_typ env in
                  (match uu____3485 with
                   | FStar_Pervasives_Native.Some t -> t
                   | FStar_Pervasives_Native.None  ->
                       let uu____3490 =
                         let uu____3491 =
                           let uu____3494 =
                             FStar_TypeChecker_Env.get_range env in
                           ("synth_by_tactic: need a type annotation when no expected type is present",
                             uu____3494) in
                         FStar_Errors.Error uu____3491 in
                       raise uu____3490) in
            let uu____3497 = FStar_TypeChecker_Env.clear_expected_typ env in
            (match uu____3497 with
             | (env',uu____3505) ->
                 let uu____3508 = tc_term env' typ in
                 (match uu____3508 with
                  | (typ1,uu____3516,g1) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                       (let uu____3519 = tc_term env' tau in
                        match uu____3519 with
                        | (tau1,c,g2) ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env'
                               g2;
                             (let uu____3531 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Tac") in
                              if uu____3531
                              then
                                let uu____3532 =
                                  FStar_Syntax_Print.term_to_string tau1 in
                                let uu____3533 =
                                  FStar_Syntax_Print.term_to_string typ1 in
                                FStar_Util.print2
                                  "Running tactic %s at return type %s\n"
                                  uu____3532 uu____3533
                              else ());
                             (let t =
                                env.FStar_TypeChecker_Env.synth env' typ1
                                  tau1 in
                              (let uu____3537 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "Tac") in
                               if uu____3537
                               then
                                 let uu____3538 =
                                   FStar_Syntax_Print.term_to_string t in
                                 FStar_Util.print1 "Got %s\n" uu____3538
                               else ());
                              FStar_TypeChecker_Util.check_uvars
                                tau1.FStar_Syntax_Syntax.pos t;
                              (let uu____3541 =
                                 FStar_Syntax_Syntax.mk_Tm_app t rest
                                   FStar_Pervasives_Native.None rng in
                               tc_term env uu____3541)))))))
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
          let uu____3557 =
            tc_check_tot_or_gtot_term env tactic
              FStar_TypeChecker_Common.t_tactic_unit in
          (match uu____3557 with
           | (tactic1,uu____3563,uu____3564) ->
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
        let uu____3593 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____3593 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____3606 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____3606
              then FStar_Util.Inl t1
              else
                (let uu____3610 =
                   let uu____3611 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____3611 in
                 FStar_Util.Inr uu____3610) in
            let is_data_ctor uu___86_3620 =
              match uu___86_3620 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____3622) -> true
              | uu____3626 -> false in
            let uu____3628 =
              (is_data_ctor dc) &&
                (let uu____3630 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____3630) in
            if uu____3628
            then
              let uu____3634 =
                let uu____3635 =
                  let uu____3638 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____3639 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____3638, uu____3639) in
                FStar_Errors.Error uu____3635 in
              raise uu____3634
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____3650 =
            let uu____3651 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____3651 in
          failwith uu____3650
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____3674 =
              let uu____3675 = FStar_Syntax_Subst.compress t1 in
              uu____3675.FStar_Syntax_Syntax.n in
            match uu____3674 with
            | FStar_Syntax_Syntax.Tm_arrow uu____3678 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____3686 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___98_3710 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___98_3710.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___98_3710.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___98_3710.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____3742 =
            let uu____3749 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____3749 with
            | FStar_Pervasives_Native.None  ->
                let uu____3757 = FStar_Syntax_Util.type_u () in
                (match uu____3757 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____3742 with
           | (t,uu____3778,g0) ->
               let uu____3786 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____3786 with
                | (e1,uu____3797,g1) ->
                    let uu____3805 =
                      let uu____3806 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____3806
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____3807 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____3805, uu____3807)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____3809 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____3818 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____3818)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____3809 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___99_3834 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___99_3834.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___99_3834.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Common.insert_bv x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____3837 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____3837 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____3850 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____3850
                       then FStar_Util.Inl t1
                       else
                         (let uu____3854 =
                            let uu____3855 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____3855 in
                          FStar_Util.Inr uu____3854) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3861;
             FStar_Syntax_Syntax.pos = uu____3862;
             FStar_Syntax_Syntax.vars = uu____3863;_},uu____3864)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____3869 =
            let uu____3870 =
              let uu____3873 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____3873) in
            FStar_Errors.Error uu____3870 in
          raise uu____3869
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____3878 =
            let uu____3879 =
              let uu____3882 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____3882) in
            FStar_Errors.Error uu____3879 in
          raise uu____3878
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3887;
             FStar_Syntax_Syntax.pos = uu____3888;
             FStar_Syntax_Syntax.vars = uu____3889;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____3897 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3897 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____3919 =
                     let uu____3920 =
                       let uu____3923 =
                         let uu____3924 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____3925 =
                           FStar_Util.string_of_int (FStar_List.length us1) in
                         let uu____3932 =
                           FStar_Util.string_of_int (FStar_List.length us') in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____3924 uu____3925 uu____3932 in
                       let uu____3939 = FStar_TypeChecker_Env.get_range env1 in
                       (uu____3923, uu____3939) in
                     FStar_Errors.Error uu____3920 in
                   raise uu____3919)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____3951 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Common.insert_fv fv' t;
                 (let e1 =
                    let uu____3955 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        (FStar_Pervasives_Native.Some
                           (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3955 us1 in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3961 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3961 with
           | ((us,t),range) ->
               ((let uu____3975 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____3975
                 then
                   let uu____3976 =
                     let uu____3977 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____3977 in
                   let uu____3978 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____3979 = FStar_Range.string_of_range range in
                   let uu____3980 = FStar_Range.string_of_use_range range in
                   let uu____3981 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____3976 uu____3978 uu____3979 uu____3980 uu____3981
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Common.insert_fv fv' t;
                 (let e1 =
                    let uu____3986 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        (FStar_Pervasives_Native.Some
                           (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3986 us in
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
          let uu____4012 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____4012 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____4021 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____4021 with
                | (env2,uu____4029) ->
                    let uu____4032 = tc_binders env2 bs1 in
                    (match uu____4032 with
                     | (bs2,env3,g,us) ->
                         let uu____4044 = tc_comp env3 c1 in
                         (match uu____4044 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___100_4057 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___100_4057.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___100_4057.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___100_4057.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____4074 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____4074 in
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
          let uu____4101 =
            let uu____4104 =
              let uu____4105 = FStar_Syntax_Syntax.mk_binder x in
              [uu____4105] in
            FStar_Syntax_Subst.open_term uu____4104 phi in
          (match uu____4101 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____4112 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____4112 with
                | (env2,uu____4120) ->
                    let uu____4123 =
                      let uu____4130 = FStar_List.hd x1 in
                      tc_binder env2 uu____4130 in
                    (match uu____4123 with
                     | (x2,env3,f1,u) ->
                         ((let uu____4147 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____4147
                           then
                             let uu____4148 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____4149 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____4150 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____4148 uu____4149 uu____4150
                           else ());
                          (let uu____4152 = FStar_Syntax_Util.type_u () in
                           match uu____4152 with
                           | (t_phi,uu____4159) ->
                               let uu____4160 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____4160 with
                                | (phi2,uu____4168,f2) ->
                                    let e1 =
                                      let uu___101_4173 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___101_4173.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___101_4173.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___101_4173.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____4188 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____4188 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____4197) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____4212 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____4212
            then
              let uu____4213 =
                FStar_Syntax_Print.term_to_string
                  (let uu___102_4216 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.tk =
                       (uu___102_4216.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___102_4216.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___102_4216.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____4213
            else ());
           (let uu____4225 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____4225 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____4233 ->
          let uu____4234 =
            let uu____4235 = FStar_Syntax_Print.term_to_string top in
            let uu____4236 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____4235
              uu____4236 in
          failwith uu____4234
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____4242 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____4243,FStar_Pervasives_Native.None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int
          (uu____4249,FStar_Pervasives_Native.Some uu____4250) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____4258 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____4262 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____4263 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____4264 ->
          FStar_TypeChecker_Common.t_range
      | uu____4265 -> raise (FStar_Errors.Error ("Unsupported constant", r))
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
      | FStar_Syntax_Syntax.Total (t,uu____4276) ->
          let uu____4283 = FStar_Syntax_Util.type_u () in
          (match uu____4283 with
           | (k,u) ->
               let uu____4291 = tc_check_tot_or_gtot_term env t k in
               (match uu____4291 with
                | (t1,uu____4299,g) ->
                    let uu____4301 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____4301, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____4303) ->
          let uu____4310 = FStar_Syntax_Util.type_u () in
          (match uu____4310 with
           | (k,u) ->
               let uu____4318 = tc_check_tot_or_gtot_term env t k in
               (match uu____4318 with
                | (t1,uu____4326,g) ->
                    let uu____4328 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____4328, u, g)))
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
            let uu____4340 =
              let uu____4341 =
                let uu____4342 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____4342 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____4341 in
            uu____4340 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____4347 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____4347 with
           | (tc1,uu____4355,f) ->
               let uu____4357 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____4357 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____4387 =
                        let uu____4388 = FStar_Syntax_Subst.compress head3 in
                        uu____4388.FStar_Syntax_Syntax.n in
                      match uu____4387 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____4391,us) -> us
                      | uu____4397 -> [] in
                    let uu____4398 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____4398 with
                     | (uu____4411,args1) ->
                         let uu____4427 =
                           let uu____4439 = FStar_List.hd args1 in
                           let uu____4448 = FStar_List.tl args1 in
                           (uu____4439, uu____4448) in
                         (match uu____4427 with
                          | (res,args2) ->
                              let uu____4490 =
                                let uu____4495 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___87_4514  ->
                                          match uu___87_4514 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____4520 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____4520 with
                                               | (env1,uu____4527) ->
                                                   let uu____4530 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____4530 with
                                                    | (e1,uu____4537,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____4495
                                  FStar_List.unzip in
                              (match uu____4490 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___103_4562 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___103_4562.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___103_4562.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____4566 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____4566 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____4569 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____4569))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____4577 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____4578 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____4584 = aux u3 in FStar_Syntax_Syntax.U_succ uu____4584
        | FStar_Syntax_Syntax.U_max us ->
            let uu____4587 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____4587
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____4591 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____4591 FStar_Pervasives_Native.snd
         | uu____4596 -> aux u)
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
            let uu____4617 =
              let uu____4618 =
                let uu____4621 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____4621, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____4618 in
            raise uu____4617 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____4675 bs2 bs_expected1 =
              match uu____4675 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____4766)) ->
                             let uu____4769 =
                               let uu____4770 =
                                 let uu____4773 =
                                   let uu____4774 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4774 in
                                 let uu____4775 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4773, uu____4775) in
                               FStar_Errors.Error uu____4770 in
                             raise uu____4769
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____4776),FStar_Pervasives_Native.None ) ->
                             let uu____4779 =
                               let uu____4780 =
                                 let uu____4783 =
                                   let uu____4784 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4784 in
                                 let uu____4785 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4783, uu____4785) in
                               FStar_Errors.Error uu____4780 in
                             raise uu____4779
                         | uu____4786 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____4790 =
                           let uu____4793 =
                             let uu____4794 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____4794.FStar_Syntax_Syntax.n in
                           match uu____4793 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4799 ->
                               ((let uu____4801 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____4801
                                 then
                                   let uu____4802 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____4802
                                 else ());
                                (let uu____4804 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____4804 with
                                 | (t,uu____4811,g1) ->
                                     let g2 =
                                       let uu____4814 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____4815 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4814
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4815 in
                                     let g3 =
                                       let uu____4817 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4817 in
                                     (t, g3))) in
                         match uu____4790 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___104_4833 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___104_4833.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___104_4833.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____4842 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____4842 in
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
                  | uu____4931 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4935 = tc_binders env1 bs in
                  match uu____4935 with
                  | (bs1,envbody,g,uu____4956) ->
                      let uu____4957 =
                        let uu____4964 =
                          let uu____4965 = FStar_Syntax_Subst.compress body1 in
                          uu____4965.FStar_Syntax_Syntax.n in
                        match uu____4964 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____4977) ->
                            let uu____5013 = tc_comp envbody c in
                            (match uu____5013 with
                             | (c1,uu____5024,g') ->
                                 let uu____5026 =
                                   tc_tactic_opt envbody tacopt in
                                 let uu____5028 =
                                   FStar_TypeChecker_Rel.conj_guard g g' in
                                 ((FStar_Pervasives_Native.Some c1),
                                   uu____5026, body1, uu____5028))
                        | uu____5031 ->
                            (FStar_Pervasives_Native.None,
                              FStar_Pervasives_Native.None, body1, g) in
                      (match uu____4957 with
                       | (copt,tacopt,body2,g1) ->
                           (FStar_Pervasives_Native.None, bs1, [], copt,
                             tacopt, envbody, body2, g1))))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____5090 =
                    let uu____5091 = FStar_Syntax_Subst.compress t2 in
                    uu____5091.FStar_Syntax_Syntax.n in
                  match uu____5090 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____5108 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____5122 -> failwith "Impossible");
                       (let uu____5126 = tc_binders env1 bs in
                        match uu____5126 with
                        | (bs1,envbody,g,uu____5148) ->
                            let uu____5149 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____5149 with
                             | (envbody1,uu____5168) ->
                                 ((FStar_Pervasives_Native.Some (t2, true)),
                                   bs1, [], FStar_Pervasives_Native.None,
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____5179;
                         FStar_Syntax_Syntax.tk = uu____5180;
                         FStar_Syntax_Syntax.pos = uu____5181;
                         FStar_Syntax_Syntax.vars = uu____5182;_},uu____5183)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____5211 -> failwith "Impossible");
                       (let uu____5215 = tc_binders env1 bs in
                        match uu____5215 with
                        | (bs1,envbody,g,uu____5237) ->
                            let uu____5238 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____5238 with
                             | (envbody1,uu____5257) ->
                                 ((FStar_Pervasives_Native.Some (t2, true)),
                                   bs1, [], FStar_Pervasives_Native.None,
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____5269) ->
                      let uu____5274 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____5274 with
                       | (uu____5303,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some (t2, false)), bs1,
                             bs', copt, tacopt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____5343 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____5343 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____5406 c_expected2 =
                               match uu____5406 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5467 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____5467)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____5484 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____5484 in
                                        let uu____5485 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____5485)
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
                                               let uu____5526 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____5526 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____5538 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____5538 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____5565 =
                                                           let uu____5581 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____5581,
                                                             subst2) in
                                                         handle_more
                                                           uu____5565
                                                           c_expected4))
                                           | uu____5590 ->
                                               let uu____5591 =
                                                 let uu____5592 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____5592 in
                                               fail uu____5591 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____5608 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____5608 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___105_5646 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___105_5646.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___105_5646.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___105_5646.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___105_5646.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___105_5646.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___105_5646.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___105_5646.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___105_5646.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___105_5646.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___105_5646.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___105_5646.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___105_5646.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___105_5646.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___105_5646.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___105_5646.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___105_5646.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___105_5646.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___105_5646.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___105_5646.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___105_5646.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___105_5646.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___105_5646.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___105_5646.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___105_5646.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___105_5646.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___105_5646.FStar_TypeChecker_Env.is_native_tactic)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____5672  ->
                                     fun uu____5673  ->
                                       match (uu____5672, uu____5673) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____5698 =
                                             let uu____5702 =
                                               let uu____5703 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____5703
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____5702 t3 in
                                           (match uu____5698 with
                                            | (t4,uu____5715,uu____5716) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____5723 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___106_5726
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___106_5726.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___106_5726.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____5723 ::
                                                        letrec_binders
                                                  | uu____5727 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____5730 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____5730 with
                            | (envbody,bs1,g,c) ->
                                let uu____5762 =
                                  let uu____5766 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____5766
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____5762 with
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
                  | uu____5802 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____5817 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____5817
                      else
                        (let uu____5819 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1 in
                         match uu____5819 with
                         | (uu____5847,bs1,uu____5849,c_opt,tacopt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some (t2, false)),
                               bs1, [], c_opt, tacopt, envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____5874 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____5874 with
          | (env1,topt) ->
              ((let uu____5886 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____5886
                then
                  let uu____5887 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____5887
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____5891 = expected_function_typ1 env1 topt body in
                match uu____5891 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____5926 =
                      tc_term
                        (let uu___107_5932 = envbody in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___107_5932.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___107_5932.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___107_5932.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___107_5932.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___107_5932.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___107_5932.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___107_5932.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___107_5932.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___107_5932.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___107_5932.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___107_5932.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___107_5932.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___107_5932.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___107_5932.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___107_5932.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___107_5932.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___107_5932.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___107_5932.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___107_5932.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___107_5932.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___107_5932.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___107_5932.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___107_5932.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___107_5932.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___107_5932.FStar_TypeChecker_Env.is_native_tactic)
                         }) body1 in
                    (match uu____5926 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body in
                         ((let uu____5941 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits") in
                           if uu____5941
                           then
                             let uu____5942 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits) in
                             let uu____5953 =
                               let uu____5954 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____5954 in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____5942 uu____5953
                           else ());
                          (let uu____5956 =
                             let uu____5960 =
                               let uu____5963 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               (body2, uu____5963) in
                             check_expected_effect
                               (let uu___108_5970 = envbody in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___108_5970.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___108_5970.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___108_5970.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___108_5970.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___108_5970.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___108_5970.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___108_5970.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___108_5970.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___108_5970.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___108_5970.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___108_5970.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___108_5970.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___108_5970.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___108_5970.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___108_5970.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___108_5970.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___108_5970.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___108_5970.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___108_5970.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___108_5970.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___108_5970.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___108_5970.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___108_5970.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___108_5970.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___108_5970.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___108_5970.FStar_TypeChecker_Env.is_native_tactic)
                                }) c_opt uu____5960 in
                           match uu____5956 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard in
                               let guard2 =
                                 let uu____5979 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____5981 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1 in
                                      Prims.op_Negation uu____5981) in
                                 if uu____5979
                                 then
                                   let uu____5982 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1 in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____5982
                                 else
                                   (let guard2 =
                                      let uu____5985 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1 in
                                      FStar_TypeChecker_Rel.close_guard env1
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____5985 in
                                    guard2) in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1 in
                               let e =
                                 FStar_Syntax_Util.abs bs1 body3
                                   (FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         (FStar_Util.dflt cbody1 c_opt))) in
                               let uu____5992 =
                                 match tfun_opt with
                                 | FStar_Pervasives_Native.Some (t,use_teq)
                                     ->
                                     let t1 = FStar_Syntax_Subst.compress t in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____6007 -> (e, t1, guard2)
                                      | uu____6015 ->
                                          let uu____6016 =
                                            if use_teq
                                            then
                                              let uu____6021 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed in
                                              (e, uu____6021)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1 in
                                          (match uu____6016 with
                                           | (e1,guard') ->
                                               let uu____6028 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard' in
                                               (e1, t1, uu____6028)))
                                 | FStar_Pervasives_Native.None  ->
                                     (e, tfun_computed, guard2) in
                               (match uu____5992 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1 in
                                    let uu____6041 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        FStar_Pervasives_Native.None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3 in
                                    (match uu____6041 with
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
              (let uu____6078 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____6078
               then
                 let uu____6079 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____6080 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____6079
                   uu____6080
               else ());
              (let monadic_application uu____6118 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____6118 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___109_6155 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___109_6155.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___109_6155.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___109_6155.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____6156 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
                       | uu____6165 ->
                           let g =
                             let uu____6170 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____6170
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____6171 =
                             let uu____6172 =
                               let uu____6175 =
                                 let uu____6176 =
                                   let uu____6177 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____6177 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____6176 in
                               FStar_Syntax_Syntax.mk_Total uu____6175 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____6172 in
                           (uu____6171, g) in
                     (match uu____6156 with
                      | (cres2,guard1) ->
                          ((let uu____6188 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____6188
                            then
                              let uu____6189 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____6189
                            else ());
                           (let cres3 =
                              let uu____6192 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____6192
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
                                   fun uu____6220  ->
                                     match uu____6220 with
                                     | ((e,q),x,c) ->
                                         let uu____6243 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____6243
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
                              let uu____6252 =
                                let uu____6253 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____6253.FStar_Syntax_Syntax.n in
                              match uu____6252 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____6257 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____6272  ->
                                         match uu____6272 with
                                         | (arg,uu____6280,uu____6281) -> arg
                                             :: args1) [] arg_comps_rev in
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
                                (let uu____6291 =
                                   let map_fun uu____6326 =
                                     match uu____6326 with
                                     | ((e,q),uu____6346,c) ->
                                         let uu____6352 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____6352
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
                                            let uu____6382 =
                                              let uu____6385 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____6385, q) in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____6382)) in
                                   let uu____6403 =
                                     let uu____6417 =
                                       let uu____6430 =
                                         let uu____6438 =
                                           let uu____6443 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____6443,
                                             FStar_Pervasives_Native.None,
                                             chead1) in
                                         uu____6438 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____6430 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____6417 in
                                   match uu____6403 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____6538 =
                                         let uu____6539 =
                                           FStar_List.hd reverse_args in
                                         FStar_Pervasives_Native.fst
                                           uu____6539 in
                                       let uu____6544 =
                                         let uu____6548 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____6548 in
                                       (lifted_args, uu____6538, uu____6544) in
                                 match uu____6291 with
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
                                     let bind_lifted_args e uu___88_6614 =
                                       match uu___88_6614 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____6656 =
                                               let uu____6659 =
                                                 let uu____6660 =
                                                   let uu____6668 =
                                                     let uu____6669 =
                                                       let uu____6670 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6670] in
                                                     FStar_Syntax_Subst.close
                                                       uu____6669 e in
                                                   ((false, [lb]),
                                                     uu____6668) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____6660 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6659 in
                                             uu____6656
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
                            let uu____6700 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp1
                                guard1 in
                            match uu____6700 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____6754 bs args1 =
                 match uu____6754 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____6834))::rest,
                         (uu____6836,FStar_Pervasives_Native.None )::uu____6837)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t in
                          let uu____6874 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____6874 with
                           | (varg,uu____6885,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____6898 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____6898) in
                               let uu____6899 =
                                 let uu____6917 =
                                   let uu____6925 =
                                     let uu____6932 =
                                       let uu____6933 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____6933
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____6932) in
                                   uu____6925 :: outargs in
                                 let uu____6943 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____6917, (arg :: arg_rets),
                                   uu____6943, fvs) in
                               tc_args head_info uu____6899 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____7003),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____7004)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____7011 ->
                                raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___110_7018 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___110_7018.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___110_7018.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____7020 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____7020
                             then
                               let uu____7021 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____7021
                             else ());
                            (let targ1 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___111_7026 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___111_7026.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___111_7026.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___111_7026.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___111_7026.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___111_7026.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___111_7026.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___111_7026.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___111_7026.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___111_7026.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___111_7026.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___111_7026.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___111_7026.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___111_7026.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___111_7026.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___111_7026.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___111_7026.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___111_7026.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___111_7026.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___111_7026.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___111_7026.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___111_7026.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___111_7026.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___111_7026.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___111_7026.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___111_7026.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___111_7026.FStar_TypeChecker_Env.is_native_tactic)
                               } in
                             (let uu____7028 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____7028
                              then
                                let uu____7029 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____7030 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____7031 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____7029 uu____7030 uu____7031
                              else ());
                             (let uu____7033 = tc_term env2 e in
                              match uu____7033 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____7050 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____7050 in
                                  let uu____7051 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____7051
                                  then
                                    let subst2 =
                                      let uu____7056 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____7056 e1 in
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
                      | (uu____7104,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____7125) ->
                          let uu____7155 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____7155 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____7178 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____7178
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____7194 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____7194 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____7208 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____7208
                                            then
                                              let uu____7209 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____7209
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____7231 when Prims.op_Negation norm1 ->
                                     let uu____7232 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____7232
                                 | uu____7233 ->
                                     let uu____7234 =
                                       let uu____7235 =
                                         let uu____7238 =
                                           let uu____7239 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____7240 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____7239 uu____7240 in
                                         let uu____7247 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____7238, uu____7247) in
                                       FStar_Errors.Error uu____7235 in
                                     raise uu____7234 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____7260 =
                   let uu____7261 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____7261.FStar_Syntax_Syntax.n in
                 match uu____7260 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____7269 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____7329 = tc_term env1 e in
                           (match uu____7329 with
                            | (e1,c,g_e) ->
                                let uu____7342 = tc_args1 env1 tl1 in
                                (match uu____7342 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7364 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7364))) in
                     let uu____7375 = tc_args1 env args in
                     (match uu____7375 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7397 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7420  ->
                                      match uu____7420 with
                                      | (uu____7428,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7397 in
                          let ml_or_tot t r1 =
                            let uu____7444 = FStar_Options.ml_ish () in
                            if uu____7444
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7447 =
                              let uu____7450 =
                                let uu____7451 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7451
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7450 in
                            ml_or_tot uu____7447 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7460 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7460
                            then
                              let uu____7461 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7462 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7463 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7461 uu____7462 uu____7463
                            else ());
                           (let uu____7466 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7466);
                           (let comp =
                              let uu____7468 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7477  ->
                                   fun out  ->
                                     match uu____7477 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7468 in
                            let uu____7486 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                (FStar_Pervasives_Native.Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7491 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7486, comp, uu____7491))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____7494;
                        FStar_Syntax_Syntax.tk = uu____7495;
                        FStar_Syntax_Syntax.pos = uu____7496;
                        FStar_Syntax_Syntax.vars = uu____7497;_},uu____7498)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____7572 = tc_term env1 e in
                           (match uu____7572 with
                            | (e1,c,g_e) ->
                                let uu____7585 = tc_args1 env1 tl1 in
                                (match uu____7585 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7607 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7607))) in
                     let uu____7618 = tc_args1 env args in
                     (match uu____7618 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7640 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7663  ->
                                      match uu____7663 with
                                      | (uu____7671,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7640 in
                          let ml_or_tot t r1 =
                            let uu____7687 = FStar_Options.ml_ish () in
                            if uu____7687
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7690 =
                              let uu____7693 =
                                let uu____7694 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7694
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7693 in
                            ml_or_tot uu____7690 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7703 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7703
                            then
                              let uu____7704 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7705 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7706 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7704 uu____7705 uu____7706
                            else ());
                           (let uu____7709 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7709);
                           (let comp =
                              let uu____7711 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7720  ->
                                   fun out  ->
                                     match uu____7720 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7711 in
                            let uu____7729 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                (FStar_Pervasives_Native.Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7734 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7729, comp, uu____7734))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____7749 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____7749 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____7785) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed (t,uu____7791,uu____7792)
                     -> check_function_app t
                 | uu____7821 ->
                     let uu____7822 =
                       let uu____7823 =
                         let uu____7826 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____7826, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____7823 in
                     raise uu____7822 in
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
                  let uu____7881 =
                    FStar_List.fold_left2
                      (fun uu____7914  ->
                         fun uu____7915  ->
                           fun uu____7916  ->
                             match (uu____7914, uu____7915, uu____7916) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____7960 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____7960 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____7972 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____7972 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____7976 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____7976) &&
                                              (let uu____7978 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____7978)) in
                                       let uu____7979 =
                                         let uu____7985 =
                                           let uu____7991 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____7991] in
                                         FStar_List.append seen uu____7985 in
                                       let uu____7996 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____7979, uu____7996, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____7881 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           (FStar_Pervasives_Native.Some
                              (res_t.FStar_Syntax_Syntax.n)) r in
                       let c1 =
                         if ghost
                         then
                           let uu____8023 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____8023
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____8025 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____8025 with | (c2,g) -> (e, c2, g)))
              | uu____8037 ->
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
        let uu____8058 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____8058 with
        | (pattern,when_clause,branch_exp) ->
            let uu____8082 = branch1 in
            (match uu____8082 with
             | (cpat,uu____8101,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____8137 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 in
                   match uu____8137 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____8154 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____8154
                         then
                           let uu____8155 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____8156 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____8155 uu____8156
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____8159 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____8159 with
                         | (env1,uu____8170) ->
                             let env11 =
                               let uu___112_8174 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___112_8174.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___112_8174.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___112_8174.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___112_8174.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___112_8174.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___112_8174.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___112_8174.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___112_8174.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___112_8174.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___112_8174.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___112_8174.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___112_8174.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___112_8174.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___112_8174.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___112_8174.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___112_8174.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___112_8174.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___112_8174.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___112_8174.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___112_8174.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___112_8174.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___112_8174.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___112_8174.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___112_8174.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___112_8174.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___112_8174.FStar_TypeChecker_Env.is_native_tactic)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____8177 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____8177
                               then
                                 let uu____8178 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____8179 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____8178 uu____8179
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t in
                               let uu____8182 = tc_tot_or_gtot_term env12 exp in
                               match uu____8182 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___113_8196 = g in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___113_8196.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___113_8196.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___113_8196.FStar_TypeChecker_Env.implicits)
                                     } in
                                   let uu____8197 =
                                     let g' =
                                       FStar_TypeChecker_Rel.teq env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t in
                                     let g2 =
                                       FStar_TypeChecker_Rel.conj_guard g1 g' in
                                     let env13 =
                                       FStar_TypeChecker_Env.set_range env12
                                         exp1.FStar_Syntax_Syntax.pos in
                                     let uu____8201 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         env13 g2 in
                                     FStar_All.pipe_right uu____8201
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1 in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____8212 =
                                       let uu____8213 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____8213 in
                                     if uu____8212
                                     then
                                       let unresolved =
                                         let uu____8220 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____8220
                                           FStar_Util.set_elements in
                                       let uu____8234 =
                                         let uu____8235 =
                                           let uu____8238 =
                                             let uu____8239 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____8240 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____8241 =
                                               let uu____8242 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____8253  ->
                                                         match uu____8253
                                                         with
                                                         | (u,uu____8257) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____8242
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____8239 uu____8240
                                               uu____8241 in
                                           (uu____8238,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____8235 in
                                       raise uu____8234
                                     else ());
                                    (let uu____8261 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____8261
                                     then
                                       let uu____8262 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____8262
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____8270 =
                   let uu____8274 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____8274
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____8270 with
                  | (scrutinee_env,uu____8287) ->
                      let uu____8290 = tc_pat true pat_t pattern in
                      (match uu____8290 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____8312 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____8327 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____8327
                                 then
                                   raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____8335 =
                                      let uu____8339 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool in
                                      tc_term uu____8339 e in
                                    match uu____8335 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g)) in
                           (match uu____8312 with
                            | (when_clause1,g_when) ->
                                let uu____8359 = tc_term pat_env branch_exp in
                                (match uu____8359 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some w ->
                                           let uu____8378 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_40  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_40) uu____8378 in
                                     let uu____8380 =
                                       let eqs =
                                         let uu____8386 =
                                           let uu____8387 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____8387 in
                                         if uu____8386
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____8392 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____8403 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____8404 ->
                                                FStar_Pervasives_Native.None
                                            | uu____8405 ->
                                                let uu____8406 =
                                                  let uu____8407 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____8407 pat_t
                                                    scrutinee_tm e in
                                                FStar_Pervasives_Native.Some
                                                  uu____8406) in
                                       let uu____8408 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch in
                                       match uu____8408 with
                                       | (c1,g_branch1) ->
                                           let uu____8418 =
                                             match (eqs, when_condition) with
                                             | uu____8425 when
                                                 let uu____8430 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation uu____8430
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
                                                 let uu____8438 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____8439 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____8438, uu____8439)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____8446 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____8446 in
                                                 let uu____8447 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____8448 =
                                                   let uu____8449 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____8449 g_when in
                                                 (uu____8447, uu____8448)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____8455 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____8455, g_when) in
                                           (match uu____8418 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____8463 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____8464 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____8463, uu____8464,
                                                  g_branch1)) in
                                     (match uu____8380 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____8477 =
                                              let uu____8478 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____8478 in
                                            if uu____8477
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____8503 =
                                                     let uu____8504 =
                                                       let uu____8505 =
                                                         let uu____8507 =
                                                           let uu____8511 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____8511 in
                                                         FStar_Pervasives_Native.snd
                                                           uu____8507 in
                                                       FStar_List.length
                                                         uu____8505 in
                                                     uu____8504 >
                                                       (Prims.parse_int "1") in
                                                   if uu____8503
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____8517 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____8517 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____8528 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None in
                                                         let disc1 =
                                                           let uu____8538 =
                                                             let uu____8539 =
                                                               let uu____8540
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____8540] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____8539 in
                                                           uu____8538
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____8545 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool in
                                                         [uu____8545]
                                                   else [] in
                                                 let fail uu____8550 =
                                                   let uu____8551 =
                                                     let uu____8552 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____8553 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____8554 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____8552 uu____8553
                                                       uu____8554 in
                                                   failwith uu____8551 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____8565) ->
                                                       head_constructor t1
                                                   | uu____8570 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____8572 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____8572
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____8574 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____8585;
                                                        FStar_Syntax_Syntax.tk
                                                          = uu____8586;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____8587;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____8588;_},uu____8589)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____8614 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____8616 =
                                                       let uu____8617 =
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____8617
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____8616]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____8618 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8624 =
                                                       let uu____8625 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8625 in
                                                     if uu____8624
                                                     then []
                                                     else
                                                       (let uu____8628 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8628)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____8630 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8632 =
                                                       let uu____8633 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8633 in
                                                     if uu____8632
                                                     then []
                                                     else
                                                       (let uu____8636 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8636)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____8655 =
                                                       let uu____8656 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8656 in
                                                     if uu____8655
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____8661 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____8683
                                                                     ->
                                                                    match uu____8683
                                                                    with
                                                                    | 
                                                                    (ei,uu____8690)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____8696
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____8696
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____8707
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8716
                                                                    =
                                                                    let uu____8717
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____8718
                                                                    =
                                                                    let uu____8719
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____8719] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8717
                                                                    uu____8718 in
                                                                    uu____8716
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____8661
                                                            FStar_List.flatten in
                                                        let uu____8727 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____8727
                                                          sub_term_guards)
                                                 | uu____8729 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____8741 =
                                                   let uu____8742 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____8742 in
                                                 if uu____8741
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____8745 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____8745 in
                                                    let uu____8748 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____8748 with
                                                    | (k,uu____8752) ->
                                                        let uu____8753 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____8753
                                                         with
                                                         | (t1,uu____8758,uu____8759)
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
                                          ((let uu____8765 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____8765
                                            then
                                              let uu____8766 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____8766
                                            else ());
                                           (let uu____8768 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____8768, branch_guard, c1,
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
          let uu____8786 = check_let_bound_def true env1 lb in
          (match uu____8786 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____8800 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____8809 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____8809, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____8812 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____8812
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____8815 =
                      let uu____8820 =
                        let uu____8826 =
                          let uu____8831 =
                            let uu____8839 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1, uu____8839) in
                          [uu____8831] in
                        FStar_TypeChecker_Util.generalize env1 uu____8826 in
                      FStar_List.hd uu____8820 in
                    match uu____8815 with
                    | (uu____8868,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____8800 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____8879 =
                      let uu____8884 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____8884
                      then
                        let uu____8889 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____8889 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____8906 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____8906
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____8907 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____8907, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____8921 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____8921
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1) in
                          let e21 =
                            let uu____8929 = FStar_Syntax_Util.is_pure_comp c in
                            if uu____8929
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
                    (match uu____8879 with
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
                           let uu____8957 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_let
                                  ((false, [lb1]), e21))
                               (FStar_Pervasives_Native.Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos in
                           (uu____8957,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____8972 -> failwith "Impossible"
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
            let uu___114_8993 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___114_8993.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___114_8993.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___114_8993.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___114_8993.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___114_8993.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___114_8993.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___114_8993.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___114_8993.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___114_8993.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___114_8993.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___114_8993.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___114_8993.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___114_8993.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___114_8993.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___114_8993.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___114_8993.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___114_8993.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___114_8993.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___114_8993.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___114_8993.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___114_8993.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___114_8993.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___114_8993.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___114_8993.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___114_8993.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___114_8993.FStar_TypeChecker_Env.is_native_tactic)
            } in
          let uu____8994 =
            let uu____9000 =
              let uu____9001 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____9001 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____9000 lb in
          (match uu____8994 with
           | (e1,uu____9013,c1,g1,annotated) ->
               let x =
                 let uu___115_9018 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___115_9018.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___115_9018.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____9019 =
                 let uu____9022 =
                   let uu____9023 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____9023] in
                 FStar_Syntax_Subst.open_term uu____9022 e2 in
               (match uu____9019 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = FStar_Pervasives_Native.fst xbinder in
                    let uu____9035 =
                      let uu____9039 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____9039 e21 in
                    (match uu____9035 with
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
                           let uu____9054 =
                             let uu____9057 =
                               let uu____9058 =
                                 let uu____9066 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____9066) in
                               FStar_Syntax_Syntax.Tm_let uu____9058 in
                             FStar_Syntax_Syntax.mk uu____9057 in
                           uu____9054
                             (FStar_Pervasives_Native.Some
                                ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____9081 =
                             let uu____9082 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____9083 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____9082
                               c1.FStar_Syntax_Syntax.res_typ uu____9083 e11 in
                           FStar_All.pipe_left
                             (fun _0_41  ->
                                FStar_TypeChecker_Common.NonTrivial _0_41)
                             uu____9081 in
                         let g21 =
                           let uu____9085 =
                             let uu____9086 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____9086 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____9085 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____9088 =
                           let uu____9089 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____9089 in
                         if uu____9088
                         then
                           let tt =
                             let uu____9095 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____9095 FStar_Option.get in
                           ((let uu____9099 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____9099
                             then
                               let uu____9100 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____9101 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____9100 uu____9101
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape FStar_Pervasives_Native.None
                                env2 [x1] cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____9106 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____9106
                             then
                               let uu____9107 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____9108 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____9107 uu____9108
                             else ());
                            (e4,
                              ((let uu___116_9111 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___116_9111.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___116_9111.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___116_9111.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____9112 -> failwith "Impossible"
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
          let uu____9133 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____9133 with
           | (lbs1,e21) ->
               let uu____9144 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____9144 with
                | (env0,topt) ->
                    let uu____9155 = build_let_rec_env true env0 lbs1 in
                    (match uu____9155 with
                     | (lbs2,rec_env) ->
                         let uu____9166 = check_let_recs rec_env lbs2 in
                         (match uu____9166 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____9178 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____9178
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____9182 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____9182
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
                                     let uu____9210 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____9234 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____9234))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____9210 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____9259  ->
                                           match uu____9259 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____9284 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____9284 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (FStar_Pervasives_Native.Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____9293 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                                match uu____9293 with
                                | (lbs5,e22) ->
                                    ((let uu____9305 =
                                        FStar_TypeChecker_Rel.discharge_guard
                                          env1 g_lbs1 in
                                      FStar_All.pipe_right uu____9305
                                        (FStar_TypeChecker_Rel.force_trivial_guard
                                           env1));
                                     (let uu____9306 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs5), e22))
                                          (FStar_Pervasives_Native.Some
                                             (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                          top.FStar_Syntax_Syntax.pos in
                                      (uu____9306, cres,
                                        FStar_TypeChecker_Rel.trivial_guard)))))))))
      | uu____9319 -> failwith "Impossible"
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
          let uu____9340 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____9340 with
           | (lbs1,e21) ->
               let uu____9351 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____9351 with
                | (env0,topt) ->
                    let uu____9362 = build_let_rec_env false env0 lbs1 in
                    (match uu____9362 with
                     | (lbs2,rec_env) ->
                         let uu____9373 = check_let_recs rec_env lbs2 in
                         (match uu____9373 with
                          | (lbs3,g_lbs) ->
                              let uu____9384 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___117_9400 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___117_9400.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___117_9400.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___118_9402 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___118_9402.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___118_9402.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___118_9402.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___118_9402.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____9384 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____9420 = tc_term env2 e21 in
                                   (match uu____9420 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____9431 =
                                            let uu____9432 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____9432 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____9431 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___119_9436 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___119_9436.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___119_9436.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___119_9436.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____9437 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____9437 with
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
                                                  uu____9462 ->
                                                  (e, cres2, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  let cres3 =
                                                    let uu___120_9467 = cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___120_9467.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___120_9467.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___120_9467.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____9470 -> failwith "Impossible"
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
          let uu____9493 =
            let uu____9496 =
              let uu____9497 = FStar_Syntax_Subst.compress t in
              uu____9497.FStar_Syntax_Syntax.n in
            let uu____9500 =
              let uu____9501 = FStar_Syntax_Subst.compress lbdef in
              uu____9501.FStar_Syntax_Syntax.n in
            (uu____9496, uu____9500) in
          match uu____9493 with
          | (FStar_Syntax_Syntax.Tm_arrow
             (formals,c),FStar_Syntax_Syntax.Tm_abs
             (actuals,uu____9507,uu____9508)) ->
              let actuals1 =
                let uu____9532 =
                  FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                FStar_TypeChecker_Util.maybe_add_implicit_binders uu____9532
                  actuals in
              (if (FStar_List.length formals) <> (FStar_List.length actuals1)
               then
                 (let actuals_msg =
                    let n1 = FStar_List.length actuals1 in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument was found"
                    else
                      (let uu____9557 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments were found"
                         uu____9557) in
                  let formals_msg =
                    let n1 = FStar_List.length formals in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument"
                    else
                      (let uu____9575 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments" uu____9575) in
                  let msg =
                    let uu____9583 = FStar_Syntax_Print.term_to_string lbtyp in
                    let uu____9584 =
                      FStar_Syntax_Print.lbname_to_string lbname in
                    FStar_Util.format4
                      "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                      uu____9583 uu____9584 formals_msg actuals_msg in
                  raise
                    (FStar_Errors.Error
                       (msg, (lbdef.FStar_Syntax_Syntax.pos))))
               else ();
               (let quals =
                  FStar_TypeChecker_Env.lookup_effect_quals env
                    (FStar_Syntax_Util.comp_effect_name c) in
                FStar_All.pipe_right quals
                  (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
          | uu____9589 ->
              let uu____9592 =
                let uu____9593 =
                  let uu____9596 =
                    let uu____9597 = FStar_Syntax_Print.term_to_string lbdef in
                    let uu____9598 = FStar_Syntax_Print.term_to_string lbtyp in
                    FStar_Util.format2
                      "Only function literals with arrow types can be defined recursively; got %s : %s"
                      uu____9597 uu____9598 in
                  (uu____9596, (lbtyp.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____9593 in
              raise uu____9592 in
        let uu____9599 =
          FStar_List.fold_left
            (fun uu____9619  ->
               fun lb  ->
                 match uu____9619 with
                 | (lbs1,env1) ->
                     let uu____9631 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____9631 with
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
                              (let uu____9645 =
                                 let uu____9649 =
                                   let uu____9650 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____9650 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___121_9657 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___121_9657.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___121_9657.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___121_9657.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___121_9657.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___121_9657.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___121_9657.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___121_9657.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___121_9657.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___121_9657.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___121_9657.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___121_9657.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___121_9657.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___121_9657.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___121_9657.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___121_9657.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___121_9657.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___121_9657.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___121_9657.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___121_9657.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___121_9657.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___121_9657.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___121_9657.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___121_9657.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___121_9657.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___121_9657.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___121_9657.FStar_TypeChecker_Env.is_native_tactic)
                                    }) t uu____9649 in
                               match uu____9645 with
                               | (t1,uu____9659,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____9663 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____9663);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____9665 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____9665
                            then
                              let uu___122_9666 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___122_9666.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___122_9666.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___122_9666.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___122_9666.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___122_9666.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___122_9666.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___122_9666.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___122_9666.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___122_9666.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___122_9666.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___122_9666.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___122_9666.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___122_9666.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___122_9666.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___122_9666.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___122_9666.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___122_9666.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___122_9666.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___122_9666.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___122_9666.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___122_9666.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___122_9666.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___122_9666.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___122_9666.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___122_9666.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___122_9666.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1) in
                          let lb1 =
                            let uu___123_9676 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___123_9676.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___123_9676.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____9599 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lbs  ->
      let uu____9690 =
        let uu____9695 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____9715 =
                     let uu____9716 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____9716.FStar_Syntax_Syntax.n in
                   match uu____9715 with
                   | FStar_Syntax_Syntax.Tm_abs uu____9719 -> ()
                   | uu____9729 ->
                       let uu____9730 =
                         let uu____9731 =
                           let uu____9734 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____9734) in
                         FStar_Errors.Error uu____9731 in
                       raise uu____9730);
                  (let uu____9735 =
                     let uu____9739 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____9739
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____9735 with
                   | (e,c,g) ->
                       ((let uu____9746 =
                           let uu____9747 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____9747 in
                         if uu____9746
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
        FStar_All.pipe_right uu____9695 FStar_List.unzip in
      match uu____9690 with
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
        let uu____9776 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____9776 with
        | (env1,uu____9786) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____9792 = check_lbtyp top_level env lb in
            (match uu____9792 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____9819 =
                     tc_maybe_toplevel_term
                       (let uu___124_9825 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___124_9825.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___124_9825.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___124_9825.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___124_9825.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___124_9825.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___124_9825.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___124_9825.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___124_9825.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___124_9825.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___124_9825.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___124_9825.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___124_9825.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___124_9825.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___124_9825.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___124_9825.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___124_9825.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___124_9825.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___124_9825.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___124_9825.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___124_9825.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___124_9825.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___124_9825.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___124_9825.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___124_9825.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___124_9825.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___124_9825.FStar_TypeChecker_Env.is_native_tactic)
                        }) e11 in
                   match uu____9819 with
                   | (e12,c1,g1) ->
                       let uu____9834 =
                         let uu____9837 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____9841  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____9837 e12 c1 wf_annot in
                       (match uu____9834 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____9851 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____9851
                              then
                                let uu____9852 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____9853 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____9854 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____9852 uu____9853 uu____9854
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
        | uu____9880 ->
            let uu____9881 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____9881 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____9908 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____9908)
                 else
                   (let uu____9913 = FStar_Syntax_Util.type_u () in
                    match uu____9913 with
                    | (k,uu____9924) ->
                        let uu____9925 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____9925 with
                         | (t2,uu____9937,g) ->
                             ((let uu____9940 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____9940
                               then
                                 let uu____9941 =
                                   let uu____9942 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____9942 in
                                 let uu____9943 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____9941 uu____9943
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____9946 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____9946))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun uu____9951  ->
      match uu____9951 with
      | (x,imp) ->
          let uu____9962 = FStar_Syntax_Util.type_u () in
          (match uu____9962 with
           | (tu,u) ->
               ((let uu____9974 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____9974
                 then
                   let uu____9975 = FStar_Syntax_Print.bv_to_string x in
                   let uu____9976 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____9977 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____9975 uu____9976 uu____9977
                 else ());
                (let uu____9979 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____9979 with
                 | (t,uu____9990,g) ->
                     let x1 =
                       ((let uu___125_9996 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___125_9996.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___125_9996.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____9998 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____9998
                       then
                         let uu____9999 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1) in
                         let uu____10000 =
                           FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____9999 uu____10000
                       else ());
                      (let uu____10002 = push_binding env x1 in
                       (x1, uu____10002, g, u))))))
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
            let uu____10053 = tc_binder env1 b in
            (match uu____10053 with
             | (b1,env',g,u) ->
                 let uu____10076 = aux env' bs2 in
                 (match uu____10076 with
                  | (bs3,env'1,g',us) ->
                      let uu____10105 =
                        let uu____10106 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____10106 in
                      ((b1 :: bs3), env'1, uu____10105, (u :: us)))) in
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
          (fun uu____10160  ->
             fun uu____10161  ->
               match (uu____10160, uu____10161) with
               | ((t,imp),(args1,g)) ->
                   let uu____10198 = tc_term env1 t in
                   (match uu____10198 with
                    | (t1,uu____10208,g') ->
                        let uu____10210 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____10210))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____10236  ->
             match uu____10236 with
             | (pats1,g) ->
                 let uu____10250 = tc_args env p in
                 (match uu____10250 with
                  | (args,g') ->
                      let uu____10258 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____10258))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let uu____10266 = tc_maybe_toplevel_term env e in
      match uu____10266 with
      | (e1,c,g) ->
          let uu____10276 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____10276
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____10286 =
               let uu____10289 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____10289
               then
                 let uu____10292 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____10292, false)
               else
                 (let uu____10294 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____10294, true)) in
             match uu____10286 with
             | (target_comp,allow_ghost) ->
                 let uu____10300 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____10300 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____10306 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____10306)
                  | uu____10307 ->
                      if allow_ghost
                      then
                        let uu____10312 =
                          let uu____10313 =
                            let uu____10316 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____10316, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____10313 in
                        raise uu____10312
                      else
                        (let uu____10321 =
                           let uu____10322 =
                             let uu____10325 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____10325, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____10322 in
                         raise uu____10321)))
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
      let uu____10338 = tc_tot_or_gtot_term env t in
      match uu____10338 with
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
      (let uu____10360 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____10360
       then
         let uu____10361 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____10361
       else ());
      (let env1 =
         let uu___126_10364 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___126_10364.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___126_10364.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___126_10364.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___126_10364.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___126_10364.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___126_10364.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___126_10364.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___126_10364.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___126_10364.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___126_10364.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___126_10364.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___126_10364.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___126_10364.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___126_10364.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___126_10364.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___126_10364.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___126_10364.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___126_10364.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___126_10364.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___126_10364.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___126_10364.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___126_10364.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___126_10364.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___126_10364.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___126_10364.FStar_TypeChecker_Env.is_native_tactic)
         } in
       let uu____10367 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____10388) ->
             let uu____10389 =
               let uu____10390 =
                 let uu____10393 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____10393) in
               FStar_Errors.Error uu____10390 in
             raise uu____10389 in
       match uu____10367 with
       | (t,c,g) ->
           let uu____10403 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____10403
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____10410 =
                let uu____10411 =
                  let uu____10414 =
                    let uu____10415 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____10415 in
                  let uu____10416 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____10414, uu____10416) in
                FStar_Errors.Error uu____10411 in
              raise uu____10410))
let level_of_type_fail env e t =
  let uu____10441 =
    let uu____10442 =
      let uu____10445 =
        let uu____10446 = FStar_Syntax_Print.term_to_string e in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____10446 t in
      let uu____10447 = FStar_TypeChecker_Env.get_range env in
      (uu____10445, uu____10447) in
    FStar_Errors.Error uu____10442 in
  raise uu____10441
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____10467 =
            let uu____10468 = FStar_Syntax_Util.unrefine t1 in
            uu____10468.FStar_Syntax_Syntax.n in
          match uu____10467 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____10472 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____10475 = FStar_Syntax_Util.type_u () in
                 match uu____10475 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___129_10481 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___129_10481.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___129_10481.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___129_10481.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___129_10481.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___129_10481.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___129_10481.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___129_10481.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___129_10481.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___129_10481.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___129_10481.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___129_10481.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___129_10481.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___129_10481.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___129_10481.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___129_10481.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___129_10481.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___129_10481.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___129_10481.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___129_10481.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___129_10481.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___129_10481.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___129_10481.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___129_10481.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___129_10481.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___129_10481.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___129_10481.FStar_TypeChecker_Env.is_native_tactic)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____10485 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____10485
                       | uu____10486 ->
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
      let uu____10497 =
        let uu____10498 = FStar_Syntax_Subst.compress e in
        uu____10498.FStar_Syntax_Syntax.n in
      match uu____10497 with
      | FStar_Syntax_Syntax.Tm_bvar uu____10503 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____10508 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____10525 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____10536) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____10551,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____10570) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10577 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10577 with | ((uu____10584,t),uu____10586) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10589,(FStar_Util.Inl t,uu____10591),uu____10592) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10628,(FStar_Util.Inr c,uu____10630),uu____10631) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____10674;
             FStar_Syntax_Syntax.pos = uu____10675;
             FStar_Syntax_Syntax.vars = uu____10676;_},us)
          ->
          let uu____10682 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10682 with
           | ((us',t),uu____10691) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____10703 =
                     let uu____10704 =
                       let uu____10707 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____10707) in
                     FStar_Errors.Error uu____10704 in
                   raise uu____10703)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10719 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____10720 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____10728) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____10745 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____10745 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____10760  ->
                      match uu____10760 with
                      | (b,uu____10764) ->
                          let uu____10765 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____10765) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____10770 = universe_of_aux env res in
                 level_of_type env res uu____10770 in
               let u_c =
                 let uu____10772 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____10772 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____10775 = universe_of_aux env trepr in
                     level_of_type env trepr uu____10775 in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____10845 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____10855 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____10879 ->
                let uu____10880 = universe_of_aux env hd3 in
                (uu____10880, args1)
            | FStar_Syntax_Syntax.Tm_name uu____10890 ->
                let uu____10891 = universe_of_aux env hd3 in
                (uu____10891, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____10901 ->
                let uu____10912 = universe_of_aux env hd3 in
                (uu____10912, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____10922 ->
                let uu____10927 = universe_of_aux env hd3 in
                (uu____10927, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____10937 ->
                let uu____10955 = universe_of_aux env hd3 in
                (uu____10955, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____10965 ->
                let uu____10970 = universe_of_aux env hd3 in
                (uu____10970, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____10980 ->
                let uu____10981 = universe_of_aux env hd3 in
                (uu____10981, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____10991 ->
                let uu____10999 = universe_of_aux env hd3 in
                (uu____10999, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____11009 ->
                let uu____11014 = universe_of_aux env hd3 in
                (uu____11014, args1)
            | FStar_Syntax_Syntax.Tm_type uu____11024 ->
                let uu____11025 = universe_of_aux env hd3 in
                (uu____11025, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____11035,hd4::uu____11037) ->
                let uu____11080 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____11080 with
                 | (uu____11090,uu____11091,hd5) ->
                     let uu____11105 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____11105 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____11140 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____11142 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____11142 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____11177 ->
                let uu____11178 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____11178 with
                 | (env1,uu____11192) ->
                     let env2 =
                       let uu___130_11196 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___130_11196.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___130_11196.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___130_11196.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___130_11196.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___130_11196.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___130_11196.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___130_11196.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___130_11196.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___130_11196.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___130_11196.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___130_11196.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___130_11196.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___130_11196.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___130_11196.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___130_11196.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___130_11196.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___130_11196.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___130_11196.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___130_11196.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___130_11196.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___130_11196.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___130_11196.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___130_11196.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___130_11196.FStar_TypeChecker_Env.is_native_tactic)
                       } in
                     ((let uu____11198 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____11198
                       then
                         let uu____11199 =
                           let uu____11200 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____11200 in
                         let uu____11201 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____11199 uu____11201
                       else ());
                      (let uu____11203 = tc_term env2 hd3 in
                       match uu____11203 with
                       | (uu____11216,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____11217;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____11219;
                                        FStar_Syntax_Syntax.comp =
                                          uu____11220;_},g)
                           ->
                           ((let uu____11230 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____11230
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____11238 = type_of_head true hd1 args in
          (match uu____11238 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____11267 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____11267 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____11304 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____11304)))
      | FStar_Syntax_Syntax.Tm_match (uu____11307,hd1::uu____11309) ->
          let uu____11352 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____11352 with
           | (uu____11355,uu____11356,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____11370,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____11404 = universe_of_aux env e in
      level_of_type env e uu____11404
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tps  ->
      let uu____11419 = tc_binders env tps in
      match uu____11419 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))