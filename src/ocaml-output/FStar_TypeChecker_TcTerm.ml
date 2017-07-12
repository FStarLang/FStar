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
        (let uu___94_1259 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___94_1259.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___94_1259.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___94_1259.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___94_1259.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___94_1259.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___94_1259.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___94_1259.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___94_1259.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___94_1259.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___94_1259.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___94_1259.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___94_1259.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___94_1259.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___94_1259.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___94_1259.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___94_1259.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___94_1259.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___94_1259.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___94_1259.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___94_1259.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___94_1259.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___94_1259.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___94_1259.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___94_1259.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___94_1259.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___94_1259.FStar_TypeChecker_Env.is_native_tactic)
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
      (let uu____1268 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1268
       then
         let uu____1269 =
           let uu____1270 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1270 in
         let uu____1271 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1269 uu____1271
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1277 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____1295 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____1300 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____1311 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____1312 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____1313 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____1314 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____1315 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____1325 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____1333 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____1338 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1344 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1344 with
            | (e2,c,g) ->
                let g1 =
                  let uu___95_1355 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___95_1355.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___95_1355.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___95_1355.FStar_TypeChecker_Env.implicits)
                  } in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1368 = FStar_Syntax_Util.type_u () in
           (match uu____1368 with
            | (t,u) ->
                let uu____1376 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1376 with
                 | (e2,c,g) ->
                     let uu____1386 =
                       let uu____1395 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____1395 with
                       | (env2,uu____1408) -> tc_pats env2 pats in
                     (match uu____1386 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___96_1429 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___96_1429.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___96_1429.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___96_1429.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____1430 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern pats1)))
                              (FStar_Pervasives_Native.Some
                                 (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____1437 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____1430, c, uu____1437))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1445 =
             let uu____1446 = FStar_Syntax_Subst.compress e1 in
             uu____1446.FStar_Syntax_Syntax.n in
           (match uu____1445 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1452,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1454;
                               FStar_Syntax_Syntax.lbtyp = uu____1455;
                               FStar_Syntax_Syntax.lbeff = uu____1456;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____1474 =
                  let uu____1478 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_TypeChecker_Common.t_unit in
                  tc_term uu____1478 e11 in
                (match uu____1474 with
                 | (e12,c1,g1) ->
                     let uu____1485 = tc_term env1 e2 in
                     (match uu____1485 with
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
                            let uu____1502 =
                              let uu____1505 =
                                let uu____1506 =
                                  let uu____1514 =
                                    let uu____1518 =
                                      let uu____1520 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_TypeChecker_Common.t_unit,
                                            e13) in
                                      [uu____1520] in
                                    (false, uu____1518) in
                                  (uu____1514, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____1506 in
                              FStar_Syntax_Syntax.mk uu____1505 in
                            uu____1502
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
                          let uu____1546 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____1546)))
            | uu____1549 ->
                let uu____1550 = tc_term env1 e1 in
                (match uu____1550 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____1570) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____1585 = tc_term env1 e1 in
           (match uu____1585 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    (FStar_Pervasives_Native.Some
                       ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____1607) ->
           let uu____1643 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____1643 with
            | (env0,uu____1651) ->
                let uu____1654 = tc_comp env0 expected_c in
                (match uu____1654 with
                 | (expected_c1,uu____1662,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____1667 =
                       let uu____1671 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____1671 e1 in
                     (match uu____1667 with
                      | (e2,c',g') ->
                          let uu____1678 =
                            let uu____1682 =
                              let uu____1685 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____1685) in
                            check_expected_effect env0
                              (FStar_Pervasives_Native.Some expected_c1)
                              uu____1682 in
                          (match uu____1678 with
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
                                 let uu____1732 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____1732 in
                               let topt1 = tc_tactic_opt env0 topt in
                               let f1 =
                                 match topt1 with
                                 | FStar_Pervasives_Native.None  -> f
                                 | FStar_Pervasives_Native.Some tactic ->
                                     FStar_TypeChecker_Rel.map_guard f
                                       (FStar_TypeChecker_Common.mk_by_tactic
                                          tactic) in
                               let uu____1737 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____1737 with
                                | (e5,c,f2) ->
                                    let uu____1747 =
                                      FStar_TypeChecker_Rel.conj_guard f1 f2 in
                                    (e5, c, uu____1747))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____1751) ->
           let uu____1787 = FStar_Syntax_Util.type_u () in
           (match uu____1787 with
            | (k,u) ->
                let uu____1795 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____1795 with
                 | (t1,uu____1803,f) ->
                     let uu____1805 =
                       let uu____1809 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____1809 e1 in
                     (match uu____1805 with
                      | (e2,c,g) ->
                          let uu____1816 =
                            let uu____1819 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (FStar_Pervasives_Native.Some
                                 (fun uu____1823  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____1819 e2 c f in
                          (match uu____1816 with
                           | (c1,f1) ->
                               let uu____1829 =
                                 let uu____1833 =
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
                                 comp_check_expected_typ env1 uu____1833 c1 in
                               (match uu____1829 with
                                | (e3,c2,f2) ->
                                    let uu____1865 =
                                      let uu____1866 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____1866 in
                                    (e3, c2, uu____1865))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____1867;
              FStar_Syntax_Syntax.pos = uu____1868;
              FStar_Syntax_Syntax.vars = uu____1869;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____1913 = FStar_Syntax_Util.head_and_args top in
           (match uu____1913 with
            | (unary_op,uu____1927) ->
                let head1 =
                  let uu____1945 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____1945 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____1981);
              FStar_Syntax_Syntax.tk = uu____1982;
              FStar_Syntax_Syntax.pos = uu____1983;
              FStar_Syntax_Syntax.vars = uu____1984;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____2028 = FStar_Syntax_Util.head_and_args top in
           (match uu____2028 with
            | (unary_op,uu____2042) ->
                let head1 =
                  let uu____2060 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                    FStar_Pervasives_Native.None uu____2060 in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____2096;
              FStar_Syntax_Syntax.pos = uu____2097;
              FStar_Syntax_Syntax.vars = uu____2098;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____2124 =
               let uu____2128 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____2128 with | (env0,uu____2136) -> tc_term env0 e1 in
             match uu____2124 with
             | (e2,c,g) ->
                 let uu____2145 = FStar_Syntax_Util.head_and_args top in
                 (match uu____2145 with
                  | (reify_op,uu____2159) ->
                      let u_c =
                        let uu____2175 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____2175 with
                        | (uu____2179,c',uu____2181) ->
                            let uu____2182 =
                              let uu____2183 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____2183.FStar_Syntax_Syntax.n in
                            (match uu____2182 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____2187 ->
                                 let uu____2188 = FStar_Syntax_Util.type_u () in
                                 (match uu____2188 with
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
                                            let uu____2197 =
                                              let uu____2198 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____2199 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____2200 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____2198 uu____2199
                                                uu____2200 in
                                            failwith uu____2197);
                                       u))) in
                      let repr =
                        let uu____2202 = c.FStar_Syntax_Syntax.comp () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____2202 u_c in
                      let e3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (reify_op, [(e2, aqual)]))
                          (FStar_Pervasives_Native.Some
                             (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____2220 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____2220
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____2221 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____2221 with
                       | (e4,c2,g') ->
                           let uu____2231 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____2231)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____2233;
              FStar_Syntax_Syntax.pos = uu____2234;
              FStar_Syntax_Syntax.vars = uu____2235;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____2267 =
               let uu____2268 =
                 let uu____2269 =
                   let uu____2272 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____2272, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____2269 in
               raise uu____2268 in
             let uu____2276 = FStar_Syntax_Util.head_and_args top in
             match uu____2276 with
             | (reflect_op,uu____2290) ->
                 let uu____2305 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____2305 with
                  | FStar_Pervasives_Native.None  -> no_reflect ()
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____2323 =
                        let uu____2324 =
                          FStar_All.pipe_right qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____2324 in
                      if uu____2323
                      then no_reflect ()
                      else
                        (let uu____2330 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____2330 with
                         | (env_no_ex,topt) ->
                             let uu____2341 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____2356 =
                                   let uu____2359 =
                                     let uu____2360 =
                                       let uu____2370 =
                                         let uu____2372 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____2373 =
                                           let uu____2375 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____2375] in
                                         uu____2372 :: uu____2373 in
                                       (repr, uu____2370) in
                                     FStar_Syntax_Syntax.Tm_app uu____2360 in
                                   FStar_Syntax_Syntax.mk uu____2359 in
                                 uu____2356 FStar_Pervasives_Native.None
                                   top.FStar_Syntax_Syntax.pos in
                               let uu____2385 =
                                 let uu____2389 =
                                   let uu____2390 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____2390
                                     FStar_Pervasives_Native.fst in
                                 tc_tot_or_gtot_term uu____2389 t in
                               match uu____2385 with
                               | (t1,uu____2407,g) ->
                                   let uu____2409 =
                                     let uu____2410 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____2410.FStar_Syntax_Syntax.n in
                                   (match uu____2409 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____2421,(res,uu____2423)::
                                         (wp,uu____2425)::[])
                                        -> (t1, res, wp, g)
                                    | uu____2459 -> failwith "Impossible") in
                             (match uu____2341 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____2483 =
                                    let uu____2486 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____2486 with
                                    | (e2,c,g) ->
                                        ((let uu____2496 =
                                            let uu____2497 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____2497 in
                                          if uu____2496
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____2503 =
                                            FStar_TypeChecker_Rel.try_teq
                                              true env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____2503 with
                                          | FStar_Pervasives_Native.None  ->
                                              ((let uu____2508 =
                                                  let uu____2512 =
                                                    let uu____2515 =
                                                      let uu____2516 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____2517 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____2516 uu____2517 in
                                                    (uu____2515,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____2512] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____2508);
                                               (let uu____2522 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____2522)))
                                          | FStar_Pervasives_Native.Some g'
                                              ->
                                              let uu____2524 =
                                                let uu____2525 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____2525 in
                                              (e2, uu____2524))) in
                                  (match uu____2483 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____2532 =
                                           let uu____2533 =
                                             let uu____2534 =
                                               let uu____2535 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____2535] in
                                             let uu____2536 =
                                               let uu____2542 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____2542] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____2534;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____2536;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____2533 in
                                         FStar_All.pipe_right uu____2532
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_app
                                              (reflect_op, [(e2, aqual)]))
                                           (FStar_Pervasives_Native.Some
                                              (res_typ.FStar_Syntax_Syntax.n))
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____2559 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____2559 with
                                        | (e4,c1,g') ->
                                            let uu____2569 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____2569))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,(tau,uu____2572)::[]) when
           FStar_Syntax_Util.is_synth_by_tactic head1 ->
           (match env1.FStar_TypeChecker_Env.expected_typ with
            | FStar_Pervasives_Native.Some typ -> tc_synth env1 typ tau
            | FStar_Pervasives_Native.None  ->
                let uu____2598 =
                  let uu____2599 =
                    let uu____2602 = FStar_TypeChecker_Env.get_range env1 in
                    ("synth_by_tactic: need a type annotation when no expected type is present",
                      uu____2602) in
                  FStar_Errors.Error uu____2599 in
                raise uu____2598)
       | FStar_Syntax_Syntax.Tm_app
           (head1,(a,uu____2608)::(tau,uu____2610)::[]) when
           FStar_Syntax_Util.is_synth_by_tactic head1 -> tc_synth env1 a tau
       | FStar_Syntax_Syntax.Tm_app
           (head1,(a,uu____2642)::uu____2643::(tau,uu____2645)::[]) when
           FStar_Syntax_Util.is_synth_by_tactic head1 -> tc_synth env1 a tau
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____2701 =
               let uu____2702 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____2702 FStar_Pervasives_Native.fst in
             FStar_All.pipe_right uu____2701 instantiate_both in
           ((let uu____2711 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____2711
             then
               let uu____2712 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____2713 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____2712
                 uu____2713
             else ());
            (let isquote =
               match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.quote_lid
                   -> true
               | uu____2717 -> false in
             let uu____2718 = tc_term (no_inst env2) head1 in
             match uu____2718 with
             | (head2,chead,g_head) ->
                 let uu____2728 =
                   let uu____2732 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____2732
                   then
                     let uu____2736 =
                       let uu____2740 =
                         FStar_TypeChecker_Env.expected_typ env0 in
                       check_short_circuit_args env2 head2 chead g_head args
                         uu____2740 in
                     match uu____2736 with
                     | (e1,c,g) ->
                         let c1 =
                           let uu____2749 =
                             ((FStar_TypeChecker_Env.should_verify env2) &&
                                (let uu____2751 =
                                   FStar_Syntax_Util.is_lcomp_partial_return
                                     c in
                                 Prims.op_Negation uu____2751))
                               &&
                               (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                           if uu____2749
                           then
                             FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                               env2 e1 c
                           else c in
                         (e1, c1, g)
                   else
                     (let env3 = if isquote then no_inst env2 else env2 in
                      let uu____2756 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env3 head2 chead g_head args
                        uu____2756) in
                 (match uu____2728 with
                  | (e1,c,g) ->
                      ((let uu____2765 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____2765
                        then
                          let uu____2766 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____2766
                        else ());
                       (let uu____2768 = comp_check_expected_typ env0 e1 c in
                        match uu____2768 with
                        | (e2,c1,g') ->
                            let gimp =
                              let uu____2779 =
                                let uu____2780 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____2780.FStar_Syntax_Syntax.n in
                              match uu____2779 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2784) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c1.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___97_2824 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___97_2824.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___97_2824.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___97_2824.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2853 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____2855 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____2855 in
                            ((let uu____2857 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____2857
                              then
                                let uu____2858 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____2859 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____2858 uu____2859
                              else ());
                             (e2, c1, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2887 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2887 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____2899 = tc_term env12 e1 in
                (match uu____2899 with
                 | (e11,c1,g1) ->
                     let uu____2909 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t)
                       | FStar_Pervasives_Native.None  ->
                           let uu____2915 = FStar_Syntax_Util.type_u () in
                           (match uu____2915 with
                            | (k,uu____2921) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____2923 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____2923, res_t)) in
                     (match uu____2909 with
                      | (env_branches,res_t) ->
                          ((let uu____2930 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____2930
                            then
                              let uu____2931 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____2931
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____2980 =
                              let uu____2983 =
                                FStar_List.fold_right
                                  (fun uu____3011  ->
                                     fun uu____3012  ->
                                       match (uu____3011, uu____3012) with
                                       | ((uu____3044,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____3077 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____3077))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____2983 with
                              | (cases,g) ->
                                  let uu____3098 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____3098, g) in
                            match uu____2980 with
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
                                           (fun uu____3159  ->
                                              match uu____3159 with
                                              | ((pat,wopt,br),uu____3175,lc,uu____3177)
                                                  ->
                                                  let uu____3184 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____3184))) in
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
                                  let uu____3232 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____3232
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____3239 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____3239 in
                                     let lb =
                                       let uu____3243 =
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
                                           uu____3243;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____3247 =
                                         let uu____3250 =
                                           let uu____3251 =
                                             let uu____3259 =
                                               let uu____3260 =
                                                 let uu____3261 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____3261] in
                                               FStar_Syntax_Subst.close
                                                 uu____3260 e_match in
                                             ((false, [lb]), uu____3259) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____3251 in
                                         FStar_Syntax_Syntax.mk uu____3250 in
                                       uu____3247
                                         (FStar_Pervasives_Native.Some
                                            ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____3275 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____3275
                                  then
                                    let uu____3276 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____3277 =
                                      let uu____3278 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____3278 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____3276 uu____3277
                                  else ());
                                 (let uu____3280 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____3280))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3283;
                FStar_Syntax_Syntax.lbunivs = uu____3284;
                FStar_Syntax_Syntax.lbtyp = uu____3285;
                FStar_Syntax_Syntax.lbeff = uu____3286;
                FStar_Syntax_Syntax.lbdef = uu____3287;_}::[]),uu____3288)
           ->
           ((let uu____3303 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3303
             then
               let uu____3304 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3304
             else ());
            (let uu____3306 =
               check_top_level_let
                 (let uu___98_3312 = env1 in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___98_3312.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___98_3312.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___98_3312.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___98_3312.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___98_3312.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___98_3312.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___98_3312.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___98_3312.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___98_3312.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___98_3312.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___98_3312.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___98_3312.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___98_3312.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___98_3312.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___98_3312.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___98_3312.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___98_3312.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___98_3312.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___98_3312.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.type_of =
                      (uu___98_3312.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___98_3312.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___98_3312.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qname_and_index =
                      (uu___98_3312.FStar_TypeChecker_Env.qname_and_index);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___98_3312.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth =
                      (uu___98_3312.FStar_TypeChecker_Env.synth);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___98_3312.FStar_TypeChecker_Env.is_native_tactic)
                  }) top in
             match uu____3306 with
             | (lax_top,l,g) ->
                 let uu____3319 = FStar_TypeChecker_Env.should_verify env1 in
                 if uu____3319
                 then check_top_level_let env1 lax_top
                 else (lax_top, l, g)))
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____3324),uu____3325) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____3335;
                FStar_Syntax_Syntax.lbunivs = uu____3336;
                FStar_Syntax_Syntax.lbtyp = uu____3337;
                FStar_Syntax_Syntax.lbeff = uu____3338;
                FStar_Syntax_Syntax.lbdef = uu____3339;_}::uu____3340),uu____3341)
           ->
           ((let uu____3357 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____3357
             then
               let uu____3358 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____3358
             else ());
            (let uu____3360 =
               check_top_level_let_rec
                 (let uu___99_3366 = env1 in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___99_3366.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___99_3366.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___99_3366.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___99_3366.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___99_3366.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___99_3366.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___99_3366.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___99_3366.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___99_3366.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___99_3366.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___99_3366.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___99_3366.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___99_3366.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___99_3366.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___99_3366.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___99_3366.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___99_3366.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___99_3366.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___99_3366.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.type_of =
                      (uu___99_3366.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___99_3366.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___99_3366.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qname_and_index =
                      (uu___99_3366.FStar_TypeChecker_Env.qname_and_index);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___99_3366.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth =
                      (uu___99_3366.FStar_TypeChecker_Env.synth);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___99_3366.FStar_TypeChecker_Env.is_native_tactic)
                  }) top in
             match uu____3360 with
             | (lax_top,l,g) ->
                 let uu____3373 = FStar_TypeChecker_Env.should_verify env1 in
                 if uu____3373
                 then check_top_level_let_rec env1 lax_top
                 else (lax_top, l, g)))
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____3378),uu____3379) ->
           check_inner_let_rec env1 top)
and tc_synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        let uu____3394 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____3394 with
        | (env',uu____3402) ->
            let uu____3405 = tc_term env' typ in
            (match uu____3405 with
             | (typ1,uu____3413,g1) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env' g1;
                  (let uu____3416 = tc_term env' tau in
                   match uu____3416 with
                   | (tau1,c,g2) ->
                       (FStar_TypeChecker_Rel.force_trivial_guard env' g2;
                        (let uu____3428 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "Tac") in
                         if uu____3428
                         then
                           let uu____3429 =
                             FStar_Syntax_Print.term_to_string tau1 in
                           let uu____3430 =
                             FStar_Syntax_Print.term_to_string typ1 in
                           FStar_Util.print2
                             "Running tactic %s at return type %s\n"
                             uu____3429 uu____3430
                         else ());
                        (let t =
                           env.FStar_TypeChecker_Env.synth env' typ1 tau1 in
                         (let uu____3434 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Tac") in
                          if uu____3434
                          then
                            let uu____3435 =
                              FStar_Syntax_Print.term_to_string t in
                            FStar_Util.print1 "Got %s\n" uu____3435
                          else ());
                         FStar_TypeChecker_Util.check_uvars
                           tau1.FStar_Syntax_Syntax.pos t;
                         tc_term env t)))))
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
          let uu____3451 =
            tc_check_tot_or_gtot_term env tactic
              FStar_TypeChecker_Common.t_tactic_unit in
          (match uu____3451 with
           | (tactic1,uu____3457,uu____3458) ->
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
        let uu____3487 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____3487 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____3500 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____3500
              then FStar_Util.Inl t1
              else
                (let uu____3504 =
                   let uu____3505 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____3505 in
                 FStar_Util.Inr uu____3504) in
            let is_data_ctor uu___86_3514 =
              match uu___86_3514 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____3516) -> true
              | uu____3520 -> false in
            let uu____3522 =
              (is_data_ctor dc) &&
                (let uu____3524 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____3524) in
            if uu____3522
            then
              let uu____3528 =
                let uu____3529 =
                  let uu____3532 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____3533 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____3532, uu____3533) in
                FStar_Errors.Error uu____3529 in
              raise uu____3528
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____3544 =
            let uu____3545 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____3545 in
          failwith uu____3544
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____3568 =
              let uu____3569 = FStar_Syntax_Subst.compress t1 in
              uu____3569.FStar_Syntax_Syntax.n in
            match uu____3568 with
            | FStar_Syntax_Syntax.Tm_arrow uu____3572 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____3580 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___100_3604 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___100_3604.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___100_3604.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___100_3604.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____3636 =
            let uu____3643 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____3643 with
            | FStar_Pervasives_Native.None  ->
                let uu____3651 = FStar_Syntax_Util.type_u () in
                (match uu____3651 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____3636 with
           | (t,uu____3672,g0) ->
               let uu____3680 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____3680 with
                | (e1,uu____3691,g1) ->
                    let uu____3699 =
                      let uu____3700 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____3700
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____3701 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____3699, uu____3701)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____3703 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____3712 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____3712)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____3703 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___101_3728 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___101_3728.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___101_3728.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Common.insert_bv x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____3731 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____3731 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____3744 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____3744
                       then FStar_Util.Inl t1
                       else
                         (let uu____3748 =
                            let uu____3749 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____3749 in
                          FStar_Util.Inr uu____3748) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3755;
             FStar_Syntax_Syntax.pos = uu____3756;
             FStar_Syntax_Syntax.vars = uu____3757;_},uu____3758)
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid
          ->
          let uu____3763 =
            let uu____3764 =
              let uu____3767 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____3767) in
            FStar_Errors.Error uu____3764 in
          raise uu____3763
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid ->
          let uu____3772 =
            let uu____3773 =
              let uu____3776 = FStar_TypeChecker_Env.get_range env1 in
              ("Badly instantiated synth_by_tactic", uu____3776) in
            FStar_Errors.Error uu____3773 in
          raise uu____3772
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3781;
             FStar_Syntax_Syntax.pos = uu____3782;
             FStar_Syntax_Syntax.vars = uu____3783;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____3791 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3791 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____3813 =
                     let uu____3814 =
                       let uu____3817 =
                         let uu____3818 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____3819 =
                           FStar_Util.string_of_int (FStar_List.length us1) in
                         let uu____3826 =
                           FStar_Util.string_of_int (FStar_List.length us') in
                         FStar_Util.format3
                           "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                           uu____3818 uu____3819 uu____3826 in
                       let uu____3833 = FStar_TypeChecker_Env.get_range env1 in
                       (uu____3817, uu____3833) in
                     FStar_Errors.Error uu____3814 in
                   raise uu____3813)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____3845 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Common.insert_fv fv' t;
                 (let e1 =
                    let uu____3849 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        (FStar_Pervasives_Native.Some
                           (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3849 us1 in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3855 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3855 with
           | ((us,t),range) ->
               ((let uu____3869 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____3869
                 then
                   let uu____3870 =
                     let uu____3871 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____3871 in
                   let uu____3872 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____3873 = FStar_Range.string_of_range range in
                   let uu____3874 = FStar_Range.string_of_use_range range in
                   let uu____3875 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____3870 uu____3872 uu____3873 uu____3874 uu____3875
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range in
                 FStar_TypeChecker_Common.insert_fv fv' t;
                 (let e1 =
                    let uu____3880 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        (FStar_Pervasives_Native.Some
                           (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3880 us in
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
          let uu____3906 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3906 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____3915 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3915 with
                | (env2,uu____3923) ->
                    let uu____3926 = tc_binders env2 bs1 in
                    (match uu____3926 with
                     | (bs2,env3,g,us) ->
                         let uu____3938 = tc_comp env3 c1 in
                         (match uu____3938 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___102_3951 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___102_3951.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___102_3951.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___102_3951.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____3968 =
                                    FStar_TypeChecker_Rel.close_guard_univs
                                      us bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____3968 in
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
          let uu____3995 =
            let uu____3998 =
              let uu____3999 = FStar_Syntax_Syntax.mk_binder x in
              [uu____3999] in
            FStar_Syntax_Subst.open_term uu____3998 phi in
          (match uu____3995 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____4006 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____4006 with
                | (env2,uu____4014) ->
                    let uu____4017 =
                      let uu____4024 = FStar_List.hd x1 in
                      tc_binder env2 uu____4024 in
                    (match uu____4017 with
                     | (x2,env3,f1,u) ->
                         ((let uu____4041 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____4041
                           then
                             let uu____4042 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____4043 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____4044 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____4042 uu____4043 uu____4044
                           else ());
                          (let uu____4046 = FStar_Syntax_Util.type_u () in
                           match uu____4046 with
                           | (t_phi,uu____4053) ->
                               let uu____4054 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____4054 with
                                | (phi2,uu____4062,f2) ->
                                    let e1 =
                                      let uu___103_4067 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___103_4067.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___103_4067.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___103_4067.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____4082 =
                                        FStar_TypeChecker_Rel.close_guard_univs
                                          [u] [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____4082 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____4091) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____4106 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____4106
            then
              let uu____4107 =
                FStar_Syntax_Print.term_to_string
                  (let uu___104_4110 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.tk =
                       (uu___104_4110.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___104_4110.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___104_4110.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____4107
            else ());
           (let uu____4119 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____4119 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____4127 ->
          let uu____4128 =
            let uu____4129 = FStar_Syntax_Print.term_to_string top in
            let uu____4130 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____4129
              uu____4130 in
          failwith uu____4128
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____4136 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____4137,FStar_Pervasives_Native.None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int
          (uu____4143,FStar_Pervasives_Native.Some uu____4144) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____4152 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____4156 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____4157 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____4158 ->
          FStar_TypeChecker_Common.t_range
      | uu____4159 -> raise (FStar_Errors.Error ("Unsupported constant", r))
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
      | FStar_Syntax_Syntax.Total (t,uu____4170) ->
          let uu____4177 = FStar_Syntax_Util.type_u () in
          (match uu____4177 with
           | (k,u) ->
               let uu____4185 = tc_check_tot_or_gtot_term env t k in
               (match uu____4185 with
                | (t1,uu____4193,g) ->
                    let uu____4195 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____4195, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____4197) ->
          let uu____4204 = FStar_Syntax_Util.type_u () in
          (match uu____4204 with
           | (k,u) ->
               let uu____4212 = tc_check_tot_or_gtot_term env t k in
               (match uu____4212 with
                | (t1,uu____4220,g) ->
                    let uu____4222 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u) in
                    (uu____4222, u, g)))
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
            let uu____4234 =
              let uu____4235 =
                let uu____4236 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____4236 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____4235 in
            uu____4234 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____4241 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____4241 with
           | (tc1,uu____4249,f) ->
               let uu____4251 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____4251 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____4281 =
                        let uu____4282 = FStar_Syntax_Subst.compress head3 in
                        uu____4282.FStar_Syntax_Syntax.n in
                      match uu____4281 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____4285,us) -> us
                      | uu____4291 -> [] in
                    let uu____4292 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____4292 with
                     | (uu____4305,args1) ->
                         let uu____4321 =
                           let uu____4333 = FStar_List.hd args1 in
                           let uu____4342 = FStar_List.tl args1 in
                           (uu____4333, uu____4342) in
                         (match uu____4321 with
                          | (res,args2) ->
                              let uu____4384 =
                                let uu____4389 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___87_4408  ->
                                          match uu___87_4408 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____4414 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____4414 with
                                               | (env1,uu____4421) ->
                                                   let uu____4424 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____4424 with
                                                    | (e1,uu____4431,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____4389
                                  FStar_List.unzip in
                              (match uu____4384 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___105_4456 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___105_4456.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___105_4456.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____4460 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____4460 with
                                     | FStar_Pervasives_Native.None  -> u
                                     | FStar_Pervasives_Native.Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____4463 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____4463))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____4471 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____4472 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____4478 = aux u3 in FStar_Syntax_Syntax.U_succ uu____4478
        | FStar_Syntax_Syntax.U_max us ->
            let uu____4481 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____4481
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____4485 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____4485 FStar_Pervasives_Native.snd
         | uu____4490 -> aux u)
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
            let uu____4511 =
              let uu____4512 =
                let uu____4515 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____4515, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____4512 in
            raise uu____4511 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____4569 bs2 bs_expected1 =
              match uu____4569 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, (FStar_List.rev out),
                         FStar_Pervasives_Native.None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (FStar_Pervasives_Native.None
                            ,FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit uu____4660)) ->
                             let uu____4663 =
                               let uu____4664 =
                                 let uu____4667 =
                                   let uu____4668 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4668 in
                                 let uu____4669 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4667, uu____4669) in
                               FStar_Errors.Error uu____4664 in
                             raise uu____4663
                         | (FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit
                            uu____4670),FStar_Pervasives_Native.None ) ->
                             let uu____4673 =
                               let uu____4674 =
                                 let uu____4677 =
                                   let uu____4678 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4678 in
                                 let uu____4679 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4677, uu____4679) in
                               FStar_Errors.Error uu____4674 in
                             raise uu____4673
                         | uu____4680 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____4684 =
                           let uu____4687 =
                             let uu____4688 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____4688.FStar_Syntax_Syntax.n in
                           match uu____4687 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4693 ->
                               ((let uu____4695 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____4695
                                 then
                                   let uu____4696 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____4696
                                 else ());
                                (let uu____4698 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____4698 with
                                 | (t,uu____4705,g1) ->
                                     let g2 =
                                       let uu____4708 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____4709 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4708
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4709 in
                                     let g3 =
                                       let uu____4711 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4711 in
                                     (t, g3))) in
                         match uu____4684 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___106_4727 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___106_4727.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___106_4727.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____4736 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____4736 in
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
                  | uu____4825 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4829 = tc_binders env1 bs in
                  match uu____4829 with
                  | (bs1,envbody,g,uu____4850) ->
                      let uu____4851 =
                        let uu____4858 =
                          let uu____4859 = FStar_Syntax_Subst.compress body1 in
                          uu____4859.FStar_Syntax_Syntax.n in
                        match uu____4858 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,(FStar_Util.Inr c,tacopt),uu____4871) ->
                            let uu____4907 = tc_comp envbody c in
                            (match uu____4907 with
                             | (c1,uu____4918,g') ->
                                 let uu____4920 =
                                   tc_tactic_opt envbody tacopt in
                                 let uu____4922 =
                                   FStar_TypeChecker_Rel.conj_guard g g' in
                                 ((FStar_Pervasives_Native.Some c1),
                                   uu____4920, body1, uu____4922))
                        | uu____4925 ->
                            (FStar_Pervasives_Native.None,
                              FStar_Pervasives_Native.None, body1, g) in
                      (match uu____4851 with
                       | (copt,tacopt,body2,g1) ->
                           (FStar_Pervasives_Native.None, bs1, [], copt,
                             tacopt, envbody, body2, g1))))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____4984 =
                    let uu____4985 = FStar_Syntax_Subst.compress t2 in
                    uu____4985.FStar_Syntax_Syntax.n in
                  match uu____4984 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____5002 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____5016 -> failwith "Impossible");
                       (let uu____5020 = tc_binders env1 bs in
                        match uu____5020 with
                        | (bs1,envbody,g,uu____5042) ->
                            let uu____5043 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____5043 with
                             | (envbody1,uu____5062) ->
                                 ((FStar_Pervasives_Native.Some (t2, true)),
                                   bs1, [], FStar_Pervasives_Native.None,
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____5073;
                         FStar_Syntax_Syntax.tk = uu____5074;
                         FStar_Syntax_Syntax.pos = uu____5075;
                         FStar_Syntax_Syntax.vars = uu____5076;_},uu____5077)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____5105 -> failwith "Impossible");
                       (let uu____5109 = tc_binders env1 bs in
                        match uu____5109 with
                        | (bs1,envbody,g,uu____5131) ->
                            let uu____5132 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____5132 with
                             | (envbody1,uu____5151) ->
                                 ((FStar_Pervasives_Native.Some (t2, true)),
                                   bs1, [], FStar_Pervasives_Native.None,
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____5163) ->
                      let uu____5168 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____5168 with
                       | (uu____5197,bs1,bs',copt,tacopt,env2,body2,g) ->
                           ((FStar_Pervasives_Native.Some (t2, false)), bs1,
                             bs', copt, tacopt, env2, body2, g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____5237 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____5237 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____5300 c_expected2 =
                               match uu____5300 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5361 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____5361)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____5378 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____5378 in
                                        let uu____5379 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____5379)
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
                                               let uu____5420 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3 in
                                               (match uu____5420 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____5432 =
                                                      check_binders env3
                                                        more_bs bs_expected4 in
                                                    (match uu____5432 with
                                                     | (env4,bs',more1,guard',subst2)
                                                         ->
                                                         let uu____5459 =
                                                           let uu____5475 =
                                                             FStar_TypeChecker_Rel.conj_guard
                                                               guard guard' in
                                                           (env4,
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____5475,
                                                             subst2) in
                                                         handle_more
                                                           uu____5459
                                                           c_expected4))
                                           | uu____5484 ->
                                               let uu____5485 =
                                                 let uu____5486 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____5486 in
                                               fail uu____5485 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____5502 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____5502 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___107_5540 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___107_5540.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___107_5540.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___107_5540.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___107_5540.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___107_5540.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___107_5540.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___107_5540.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___107_5540.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___107_5540.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___107_5540.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___107_5540.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___107_5540.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___107_5540.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___107_5540.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___107_5540.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___107_5540.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___107_5540.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___107_5540.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___107_5540.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___107_5540.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___107_5540.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___107_5540.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___107_5540.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___107_5540.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___107_5540.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___107_5540.FStar_TypeChecker_Env.is_native_tactic)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____5569  ->
                                     fun uu____5570  ->
                                       match (uu____5569, uu____5570) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____5605 =
                                             let uu____5609 =
                                               let uu____5610 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____5610
                                                 FStar_Pervasives_Native.fst in
                                             tc_term uu____5609 t3 in
                                           (match uu____5605 with
                                            | (t4,uu____5622,uu____5623) ->
                                                let unames =
                                                  let uu____5625 =
                                                    let uu____5629 =
                                                      match l with
                                                      | FStar_Util.Inr fvar1
                                                          ->
                                                          FStar_Syntax_Syntax.lid_of_fv
                                                            fvar1
                                                      | FStar_Util.Inl bvar
                                                          ->
                                                          FStar_Ident.lid_of_ids
                                                            [bvar.FStar_Syntax_Syntax.ppname] in
                                                    FStar_TypeChecker_Env.lookup_definition
                                                      [FStar_TypeChecker_Env.Always]
                                                      env2 uu____5629 in
                                                  match uu____5625 with
                                                  | FStar_Pervasives_Native.Some
                                                      (x,uu____5633) -> x
                                                  | uu____5636 -> [] in
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l (unames, t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____5645 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___108_5648
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___108_5648.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___108_5648.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____5645 ::
                                                        letrec_binders
                                                  | uu____5649 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____5654 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____5654 with
                            | (envbody,bs1,g,c) ->
                                let uu____5686 =
                                  let uu____5690 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____5690
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____5686 with
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
                  | uu____5726 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____5741 =
                          FStar_TypeChecker_Normalize.unfold_whnf env1 t2 in
                        as_function_typ true uu____5741
                      else
                        (let uu____5743 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1 in
                         match uu____5743 with
                         | (uu____5771,bs1,uu____5773,c_opt,tacopt,envbody,body2,g)
                             ->
                             ((FStar_Pervasives_Native.Some (t2, false)),
                               bs1, [], c_opt, tacopt, envbody, body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____5798 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____5798 with
          | (env1,topt) ->
              ((let uu____5810 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____5810
                then
                  let uu____5811 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____5811
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____5815 = expected_function_typ1 env1 topt body in
                match uu____5815 with
                | (tfun_opt,bs1,letrec_binders,c_opt,tacopt,envbody,body1,g)
                    ->
                    let uu____5850 =
                      tc_term
                        (let uu___109_5856 = envbody in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___109_5856.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___109_5856.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___109_5856.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___109_5856.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___109_5856.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___109_5856.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___109_5856.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___109_5856.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___109_5856.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___109_5856.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___109_5856.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___109_5856.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___109_5856.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___109_5856.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___109_5856.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___109_5856.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___109_5856.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___109_5856.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___109_5856.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___109_5856.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___109_5856.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___109_5856.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___109_5856.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___109_5856.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___109_5856.FStar_TypeChecker_Env.is_native_tactic)
                         }) body1 in
                    (match uu____5850 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body in
                         ((let uu____5865 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits") in
                           if uu____5865
                           then
                             let uu____5866 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits) in
                             let uu____5877 =
                               let uu____5878 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____5878 in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____5866 uu____5877
                           else ());
                          (let uu____5880 =
                             let uu____5884 =
                               let uu____5887 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               (body2, uu____5887) in
                             check_expected_effect
                               (let uu___110_5894 = envbody in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___110_5894.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___110_5894.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___110_5894.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___110_5894.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___110_5894.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___110_5894.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___110_5894.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___110_5894.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___110_5894.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___110_5894.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___110_5894.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___110_5894.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___110_5894.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___110_5894.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___110_5894.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___110_5894.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___110_5894.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___110_5894.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___110_5894.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___110_5894.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___110_5894.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___110_5894.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___110_5894.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___110_5894.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___110_5894.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___110_5894.FStar_TypeChecker_Env.is_native_tactic)
                                }) c_opt uu____5884 in
                           match uu____5880 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard in
                               let guard2 =
                                 let uu____5903 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____5905 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1 in
                                      Prims.op_Negation uu____5905) in
                                 if uu____5903
                                 then
                                   let uu____5906 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1 in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____5906
                                 else
                                   (let guard2 =
                                      let uu____5909 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1 in
                                      FStar_TypeChecker_Rel.close_guard env1
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____5909 in
                                    guard2) in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1 in
                               let e =
                                 FStar_Syntax_Util.abs bs1 body3
                                   (FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Util.residual_comp_of_comp
                                         (FStar_Util.dflt cbody1 c_opt))) in
                               let uu____5916 =
                                 match tfun_opt with
                                 | FStar_Pervasives_Native.Some (t,use_teq)
                                     ->
                                     let t1 = FStar_Syntax_Subst.compress t in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____5931 -> (e, t1, guard2)
                                      | uu____5939 ->
                                          let uu____5940 =
                                            if use_teq
                                            then
                                              let uu____5945 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed in
                                              (e, uu____5945)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1 in
                                          (match uu____5940 with
                                           | (e1,guard') ->
                                               let uu____5952 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard' in
                                               (e1, t1, uu____5952)))
                                 | FStar_Pervasives_Native.None  ->
                                     (e, tfun_computed, guard2) in
                               (match uu____5916 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1 in
                                    let uu____5965 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        FStar_Pervasives_Native.None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3 in
                                    (match uu____5965 with
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
              (let uu____6002 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____6002
               then
                 let uu____6003 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____6004 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____6003
                   uu____6004
               else ());
              (let monadic_application uu____6042 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____6042 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___111_6079 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___111_6079.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___111_6079.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___111_6079.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____6080 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           (cres2, g)
                       | uu____6089 ->
                           let g =
                             let uu____6094 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____6094
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____6095 =
                             let uu____6096 =
                               let uu____6099 =
                                 let uu____6100 =
                                   let uu____6101 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____6101 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____6100 in
                               FStar_Syntax_Syntax.mk_Total uu____6099 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____6096 in
                           (uu____6095, g) in
                     (match uu____6080 with
                      | (cres2,guard1) ->
                          ((let uu____6112 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____6112
                            then
                              let uu____6113 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____6113
                            else ());
                           (let cres3 =
                              let uu____6116 =
                                FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                  cres2 in
                              if uu____6116
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
                                   fun uu____6144  ->
                                     match uu____6144 with
                                     | ((e,q),x,c) ->
                                         let uu____6167 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____6167
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
                              let uu____6176 =
                                let uu____6177 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____6177.FStar_Syntax_Syntax.n in
                              match uu____6176 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_Or)
                              | uu____6181 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____6196  ->
                                         match uu____6196 with
                                         | (arg,uu____6204,uu____6205) -> arg
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
                                (let uu____6215 =
                                   let map_fun uu____6250 =
                                     match uu____6250 with
                                     | ((e,q),uu____6270,c) ->
                                         let uu____6276 =
                                           FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                             c in
                                         if uu____6276
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
                                            let uu____6306 =
                                              let uu____6309 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              (uu____6309, q) in
                                            ((FStar_Pervasives_Native.Some
                                                (x,
                                                  (c.FStar_Syntax_Syntax.eff_name),
                                                  (c.FStar_Syntax_Syntax.res_typ),
                                                  e1)), uu____6306)) in
                                   let uu____6327 =
                                     let uu____6341 =
                                       let uu____6354 =
                                         let uu____6362 =
                                           let uu____6367 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____6367,
                                             FStar_Pervasives_Native.None,
                                             chead1) in
                                         uu____6362 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____6354 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____6341 in
                                   match uu____6327 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____6462 =
                                         let uu____6463 =
                                           FStar_List.hd reverse_args in
                                         FStar_Pervasives_Native.fst
                                           uu____6463 in
                                       let uu____6468 =
                                         let uu____6472 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____6472 in
                                       (lifted_args, uu____6462, uu____6468) in
                                 match uu____6215 with
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
                                     let bind_lifted_args e uu___88_6538 =
                                       match uu___88_6538 with
                                       | FStar_Pervasives_Native.None  -> e
                                       | FStar_Pervasives_Native.Some
                                           (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____6580 =
                                               let uu____6583 =
                                                 let uu____6584 =
                                                   let uu____6592 =
                                                     let uu____6593 =
                                                       let uu____6594 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6594] in
                                                     FStar_Syntax_Subst.close
                                                       uu____6593 e in
                                                   ((false, [lb]),
                                                     uu____6592) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____6584 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6583 in
                                             uu____6580
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
                            let uu____6624 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                FStar_Pervasives_Native.None env app comp1
                                guard1 in
                            match uu____6624 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____6678 bs args1 =
                 match uu____6678 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____6758))::rest,
                         (uu____6760,FStar_Pervasives_Native.None )::uu____6761)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t in
                          let uu____6798 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____6798 with
                           | (varg,uu____6809,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____6822 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____6822) in
                               let uu____6823 =
                                 let uu____6841 =
                                   let uu____6849 =
                                     let uu____6856 =
                                       let uu____6857 =
                                         FStar_Syntax_Syntax.mk_Total t1 in
                                       FStar_All.pipe_right uu____6857
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     (arg, FStar_Pervasives_Native.None,
                                       uu____6856) in
                                   uu____6849 :: outargs in
                                 let uu____6867 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2, uu____6841, (arg :: arg_rets),
                                   uu____6867, fvs) in
                               tc_args head_info uu____6823 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____6927),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____6928)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____6935 ->
                                raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___112_6942 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___112_6942.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___112_6942.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____6944 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____6944
                             then
                               let uu____6945 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____6945
                             else ());
                            (let targ1 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___113_6950 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___113_6950.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___113_6950.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___113_6950.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___113_6950.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___113_6950.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___113_6950.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___113_6950.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___113_6950.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___113_6950.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___113_6950.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___113_6950.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___113_6950.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___113_6950.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___113_6950.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___113_6950.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___113_6950.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___113_6950.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___113_6950.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___113_6950.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___113_6950.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___113_6950.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___113_6950.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___113_6950.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___113_6950.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___113_6950.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___113_6950.FStar_TypeChecker_Env.is_native_tactic)
                               } in
                             (let uu____6952 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____6952
                              then
                                let uu____6953 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____6954 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____6955 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____6953 uu____6954 uu____6955
                              else ());
                             (let uu____6957 = tc_term env2 e in
                              match uu____6957 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let xterm =
                                    let uu____6974 =
                                      FStar_Syntax_Syntax.bv_to_name x1 in
                                    FStar_Syntax_Syntax.as_arg uu____6974 in
                                  let uu____6975 =
                                    (FStar_Syntax_Util.is_tot_or_gtot_lcomp c)
                                      ||
                                      (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name) in
                                  if uu____6975
                                  then
                                    let subst2 =
                                      let uu____6980 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____6980 e1 in
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
                      | (uu____7028,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____7049) ->
                          let uu____7079 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____7079 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____7102 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____7102
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____7118 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____7118 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____7132 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____7132
                                            then
                                              let uu____7133 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____7133
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____7155 when Prims.op_Negation norm1 ->
                                     let uu____7156 =
                                       FStar_TypeChecker_Normalize.unfold_whnf
                                         env tres1 in
                                     aux true uu____7156
                                 | uu____7157 ->
                                     let uu____7158 =
                                       let uu____7159 =
                                         let uu____7162 =
                                           let uu____7163 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____7164 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____7163 uu____7164 in
                                         let uu____7171 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____7162, uu____7171) in
                                       FStar_Errors.Error uu____7159 in
                                     raise uu____7158 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app tf =
                 let uu____7184 =
                   let uu____7185 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf in
                   uu____7185.FStar_Syntax_Syntax.n in
                 match uu____7184 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____7193 ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____7253 = tc_term env1 e in
                           (match uu____7253 with
                            | (e1,c,g_e) ->
                                let uu____7266 = tc_args1 env1 tl1 in
                                (match uu____7266 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7288 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7288))) in
                     let uu____7299 = tc_args1 env args in
                     (match uu____7299 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7321 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7344  ->
                                      match uu____7344 with
                                      | (uu____7352,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7321 in
                          let ml_or_tot t r1 =
                            let uu____7368 = FStar_Options.ml_ish () in
                            if uu____7368
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7371 =
                              let uu____7374 =
                                let uu____7375 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7375
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7374 in
                            ml_or_tot uu____7371 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7384 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7384
                            then
                              let uu____7385 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7386 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7387 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7385 uu____7386 uu____7387
                            else ());
                           (let uu____7390 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7390);
                           (let comp =
                              let uu____7392 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7401  ->
                                   fun out  ->
                                     match uu____7401 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7392 in
                            let uu____7410 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                (FStar_Pervasives_Native.Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7415 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7410, comp, uu____7415))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____7418;
                        FStar_Syntax_Syntax.tk = uu____7419;
                        FStar_Syntax_Syntax.pos = uu____7420;
                        FStar_Syntax_Syntax.vars = uu____7421;_},uu____7422)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____7496 = tc_term env1 e in
                           (match uu____7496 with
                            | (e1,c,g_e) ->
                                let uu____7509 = tc_args1 env1 tl1 in
                                (match uu____7509 with
                                 | (args2,comps,g_rest) ->
                                     let uu____7531 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____7531))) in
                     let uu____7542 = tc_args1 env args in
                     (match uu____7542 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____7564 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____7587  ->
                                      match uu____7587 with
                                      | (uu____7595,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            FStar_Pervasives_Native.None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____7564 in
                          let ml_or_tot t r1 =
                            let uu____7611 = FStar_Options.ml_ish () in
                            if uu____7611
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7614 =
                              let uu____7617 =
                                let uu____7618 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7618
                                  FStar_Pervasives_Native.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7617 in
                            ml_or_tot uu____7614 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7627 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7627
                            then
                              let uu____7628 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7629 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7630 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7628 uu____7629 uu____7630
                            else ());
                           (let uu____7633 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7633);
                           (let comp =
                              let uu____7635 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7644  ->
                                   fun out  ->
                                     match uu____7644 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           FStar_Pervasives_Native.None c
                                           (FStar_Pervasives_Native.None,
                                             out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7635 in
                            let uu____7653 =
                              FStar_Syntax_Syntax.mk_Tm_app head1 args1
                                (FStar_Pervasives_Native.Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7658 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7653, comp, uu____7658))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____7673 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____7673 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____7709) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort
                 | FStar_Syntax_Syntax.Tm_ascribed (t,uu____7715,uu____7716)
                     -> check_function_app t
                 | uu____7745 ->
                     let uu____7746 =
                       let uu____7747 =
                         let uu____7750 =
                           FStar_TypeChecker_Err.expected_function_typ env tf in
                         (uu____7750, (head1.FStar_Syntax_Syntax.pos)) in
                       FStar_Errors.Error uu____7747 in
                     raise uu____7746 in
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
                  let uu____7805 =
                    FStar_List.fold_left2
                      (fun uu____7838  ->
                         fun uu____7839  ->
                           fun uu____7840  ->
                             match (uu____7838, uu____7839, uu____7840) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____7884 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____7884 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____7896 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____7896 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____7900 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____7900) &&
                                              (let uu____7902 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____7902)) in
                                       let uu____7903 =
                                         let uu____7909 =
                                           let uu____7915 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____7915] in
                                         FStar_List.append seen uu____7909 in
                                       let uu____7920 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____7903, uu____7920, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____7805 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           (FStar_Pervasives_Native.Some
                              (res_t.FStar_Syntax_Syntax.n)) r in
                       let c1 =
                         if ghost
                         then
                           let uu____7947 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____7947
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____7949 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard in
                       (match uu____7949 with | (c2,g) -> (e, c2, g)))
              | uu____7961 ->
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
        let uu____7982 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____7982 with
        | (pattern,when_clause,branch_exp) ->
            let uu____8006 = branch1 in
            (match uu____8006 with
             | (cpat,uu____8025,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____8061 =
                     FStar_TypeChecker_Util.pat_as_exp allow_implicits env p0 in
                   match uu____8061 with
                   | (pat_bvs1,exp,p) ->
                       ((let uu____8078 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____8078
                         then
                           let uu____8079 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____8080 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____8079 uu____8080
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____8083 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____8083 with
                         | (env1,uu____8094) ->
                             let env11 =
                               let uu___114_8098 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___114_8098.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___114_8098.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___114_8098.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___114_8098.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___114_8098.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___114_8098.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___114_8098.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___114_8098.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___114_8098.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___114_8098.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___114_8098.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___114_8098.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___114_8098.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___114_8098.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___114_8098.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___114_8098.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___114_8098.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___114_8098.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___114_8098.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___114_8098.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___114_8098.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___114_8098.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___114_8098.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___114_8098.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___114_8098.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___114_8098.FStar_TypeChecker_Env.is_native_tactic)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             ((let uu____8101 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.High in
                               if uu____8101
                               then
                                 let uu____8102 =
                                   FStar_Syntax_Print.term_to_string exp in
                                 let uu____8103 =
                                   FStar_Syntax_Print.term_to_string pat_t in
                                 FStar_Util.print2
                                   "Checking pattern expression %s against expected type %s\n"
                                   uu____8102 uu____8103
                               else ());
                              (let env12 =
                                 FStar_TypeChecker_Env.set_expected_typ env11
                                   expected_pat_t in
                               let uu____8106 = tc_tot_or_gtot_term env12 exp in
                               match uu____8106 with
                               | (exp1,lc,g) ->
                                   let g1 =
                                     let uu___115_8120 = g in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___115_8120.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___115_8120.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___115_8120.FStar_TypeChecker_Env.implicits)
                                     } in
                                   let uu____8121 =
                                     let g' =
                                       FStar_TypeChecker_Rel.teq env12
                                         lc.FStar_Syntax_Syntax.res_typ
                                         expected_pat_t in
                                     let g2 =
                                       FStar_TypeChecker_Rel.conj_guard g1 g' in
                                     let env13 =
                                       FStar_TypeChecker_Env.set_range env12
                                         exp1.FStar_Syntax_Syntax.pos in
                                     let uu____8125 =
                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                         env13 g2 in
                                     FStar_All.pipe_right uu____8125
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   let norm_exp =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.Beta]
                                       env12 exp1 in
                                   let uvs1 =
                                     FStar_Syntax_Free.uvars norm_exp in
                                   let uvs2 =
                                     FStar_Syntax_Free.uvars expected_pat_t in
                                   ((let uu____8136 =
                                       let uu____8137 =
                                         FStar_Util.set_is_subset_of uvs1
                                           uvs2 in
                                       FStar_All.pipe_left Prims.op_Negation
                                         uu____8137 in
                                     if uu____8136
                                     then
                                       let unresolved =
                                         let uu____8144 =
                                           FStar_Util.set_difference uvs1
                                             uvs2 in
                                         FStar_All.pipe_right uu____8144
                                           FStar_Util.set_elements in
                                       let uu____8158 =
                                         let uu____8159 =
                                           let uu____8162 =
                                             let uu____8163 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env norm_exp in
                                             let uu____8164 =
                                               FStar_TypeChecker_Normalize.term_to_string
                                                 env expected_pat_t in
                                             let uu____8165 =
                                               let uu____8166 =
                                                 FStar_All.pipe_right
                                                   unresolved
                                                   (FStar_List.map
                                                      (fun uu____8177  ->
                                                         match uu____8177
                                                         with
                                                         | (u,uu____8181) ->
                                                             FStar_Syntax_Print.uvar_to_string
                                                               u)) in
                                               FStar_All.pipe_right
                                                 uu____8166
                                                 (FStar_String.concat ", ") in
                                             FStar_Util.format3
                                               "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                               uu____8163 uu____8164
                                               uu____8165 in
                                           (uu____8162,
                                             (p.FStar_Syntax_Syntax.p)) in
                                         FStar_Errors.Error uu____8159 in
                                       raise uu____8158
                                     else ());
                                    (let uu____8185 =
                                       FStar_TypeChecker_Env.debug env
                                         FStar_Options.High in
                                     if uu____8185
                                     then
                                       let uu____8186 =
                                         FStar_TypeChecker_Normalize.term_to_string
                                           env exp1 in
                                       FStar_Util.print1
                                         "Done checking pattern expression %s\n"
                                         uu____8186
                                     else ());
                                    (let p1 =
                                       FStar_TypeChecker_Util.decorate_pattern
                                         env p exp1 in
                                     (p1, pat_bvs1, pat_env, exp1, norm_exp))))))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____8194 =
                   let uu____8198 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____8198
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____8194 with
                  | (scrutinee_env,uu____8211) ->
                      let uu____8214 = tc_pat true pat_t pattern in
                      (match uu____8214 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp) ->
                           let uu____8236 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Rel.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____8251 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____8251
                                 then
                                   raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____8259 =
                                      let uu____8263 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool in
                                      tc_term uu____8263 e in
                                    match uu____8259 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g)) in
                           (match uu____8236 with
                            | (when_clause1,g_when) ->
                                let uu____8283 = tc_term pat_env branch_exp in
                                (match uu____8283 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | FStar_Pervasives_Native.None  ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some w ->
                                           let uu____8302 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Util.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_40  ->
                                                FStar_Pervasives_Native.Some
                                                  _0_40) uu____8302 in
                                     let uu____8304 =
                                       let eqs =
                                         let uu____8310 =
                                           let uu____8311 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____8311 in
                                         if uu____8310
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let e =
                                              FStar_Syntax_Subst.compress
                                                pat_exp in
                                            match e.FStar_Syntax_Syntax.n
                                            with
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____8316 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_constant
                                                uu____8327 ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Syntax_Syntax.Tm_fvar
                                                uu____8328 ->
                                                FStar_Pervasives_Native.None
                                            | uu____8329 ->
                                                let uu____8330 =
                                                  let uu____8331 =
                                                    env.FStar_TypeChecker_Env.universe_of
                                                      env pat_t in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____8331 pat_t
                                                    scrutinee_tm e in
                                                FStar_Pervasives_Native.Some
                                                  uu____8330) in
                                       let uu____8332 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           FStar_Pervasives_Native.None env
                                           branch_exp1 c g_branch in
                                       match uu____8332 with
                                       | (c1,g_branch1) ->
                                           let uu____8342 =
                                             match (eqs, when_condition) with
                                             | uu____8349 when
                                                 let uu____8354 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation uu____8354
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
                                                 let uu____8362 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____8363 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____8362, uu____8363)
                                             | (FStar_Pervasives_Native.Some
                                                f,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____8370 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____8370 in
                                                 let uu____8371 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____8372 =
                                                   let uu____8373 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____8373 g_when in
                                                 (uu____8371, uu____8372)
                                             | (FStar_Pervasives_Native.None
                                                ,FStar_Pervasives_Native.Some
                                                w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____8379 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____8379, g_when) in
                                           (match uu____8342 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____8387 =
                                                  FStar_TypeChecker_Util.close_lcomp
                                                    env pat_bvs1 c_weak in
                                                let uu____8388 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    env binders g_when_weak in
                                                (uu____8387, uu____8388,
                                                  g_branch1)) in
                                     (match uu____8304 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____8401 =
                                              let uu____8402 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____8402 in
                                            if uu____8401
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp1 =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____8427 =
                                                     let uu____8428 =
                                                       let uu____8429 =
                                                         let uu____8431 =
                                                           let uu____8435 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____8435 in
                                                         FStar_Pervasives_Native.snd
                                                           uu____8431 in
                                                       FStar_List.length
                                                         uu____8429 in
                                                     uu____8428 >
                                                       (Prims.parse_int "1") in
                                                   if uu____8427
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____8441 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____8441 with
                                                     | FStar_Pervasives_Native.None
                                                          -> []
                                                     | uu____8452 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             FStar_Pervasives_Native.None in
                                                         let disc1 =
                                                           let uu____8462 =
                                                             let uu____8463 =
                                                               let uu____8464
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____8464] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____8463 in
                                                           uu____8462
                                                             FStar_Pervasives_Native.None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____8469 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Util.exp_true_bool in
                                                         [uu____8469]
                                                   else [] in
                                                 let fail uu____8474 =
                                                   let uu____8475 =
                                                     let uu____8476 =
                                                       FStar_Range.string_of_range
                                                         pat_exp1.FStar_Syntax_Syntax.pos in
                                                     let uu____8477 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp1 in
                                                     let uu____8478 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp1 in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____8476 uu____8477
                                                       uu____8478 in
                                                   failwith uu____8475 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____8489) ->
                                                       head_constructor t1
                                                   | uu____8494 -> fail () in
                                                 let pat_exp2 =
                                                   let uu____8496 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp1 in
                                                   FStar_All.pipe_right
                                                     uu____8496
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                     uu____8498 -> []
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     ({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_uvar
                                                          uu____8509;
                                                        FStar_Syntax_Syntax.tk
                                                          = uu____8510;
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____8511;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____8512;_},uu____8513)
                                                     -> []
                                                 | FStar_Syntax_Syntax.Tm_name
                                                     uu____8538 -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____8540 =
                                                       let uu____8541 =
                                                         tc_constant
                                                           pat_exp2.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____8541
                                                         scrutinee_tm1
                                                         pat_exp2 in
                                                     [uu____8540]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                     uu____8542 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8548 =
                                                       let uu____8549 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8549 in
                                                     if uu____8548
                                                     then []
                                                     else
                                                       (let uu____8552 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8552)
                                                 | FStar_Syntax_Syntax.Tm_fvar
                                                     uu____8554 ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp2 in
                                                     let uu____8556 =
                                                       let uu____8557 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8557 in
                                                     if uu____8556
                                                     then []
                                                     else
                                                       (let uu____8560 =
                                                          head_constructor
                                                            pat_exp2 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8560)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____8579 =
                                                       let uu____8580 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8580 in
                                                     if uu____8579
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____8585 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____8607
                                                                     ->
                                                                    match uu____8607
                                                                    with
                                                                    | 
                                                                    (ei,uu____8614)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____8620
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____8620
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     -> []
                                                                    | 
                                                                    uu____8631
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8640
                                                                    =
                                                                    let uu____8641
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    FStar_Pervasives_Native.None in
                                                                    let uu____8642
                                                                    =
                                                                    let uu____8643
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____8643] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8641
                                                                    uu____8642 in
                                                                    uu____8640
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____8585
                                                            FStar_List.flatten in
                                                        let uu____8651 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____8651
                                                          sub_term_guards)
                                                 | uu____8653 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____8665 =
                                                   let uu____8666 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____8666 in
                                                 if uu____8665
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Parser_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____8669 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____8669 in
                                                    let uu____8672 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____8672 with
                                                    | (k,uu____8676) ->
                                                        let uu____8677 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____8677
                                                         with
                                                         | (t1,uu____8682,uu____8683)
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
                                          ((let uu____8689 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____8689
                                            then
                                              let uu____8690 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____8690
                                            else ());
                                           (let uu____8692 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____8692, branch_guard, c1,
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
          let uu____8710 = check_let_bound_def true env1 lb in
          (match uu____8710 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____8724 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____8733 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1 in
                   (g1, uu____8733, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____8736 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____8736
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____8739 =
                      let uu____8744 =
                        let uu____8750 =
                          let uu____8755 =
                            let uu____8763 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1, uu____8763) in
                          [uu____8755] in
                        FStar_TypeChecker_Util.generalize env1 uu____8750 in
                      FStar_List.hd uu____8744 in
                    match uu____8739 with
                    | (uu____8792,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____8724 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____8803 =
                      let uu____8808 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____8808
                      then
                        let uu____8813 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____8813 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____8830 =
                                   FStar_TypeChecker_Env.get_range env1 in
                                 FStar_Errors.warn uu____8830
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____8831 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos in
                                 (uu____8831, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____8845 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____8845
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1) in
                          let e21 =
                            let uu____8853 = FStar_Syntax_Util.is_pure_comp c in
                            if uu____8853
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
                    (match uu____8803 with
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
                           let uu____8881 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_let
                                  ((false, [lb1]), e21))
                               (FStar_Pervasives_Native.Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos in
                           (uu____8881,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____8896 -> failwith "Impossible"
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
            let uu___116_8917 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___116_8917.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___116_8917.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___116_8917.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___116_8917.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___116_8917.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___116_8917.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___116_8917.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___116_8917.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___116_8917.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___116_8917.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___116_8917.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___116_8917.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___116_8917.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___116_8917.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___116_8917.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___116_8917.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___116_8917.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___116_8917.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___116_8917.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___116_8917.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___116_8917.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___116_8917.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___116_8917.FStar_TypeChecker_Env.qname_and_index);
              FStar_TypeChecker_Env.proof_ns =
                (uu___116_8917.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth =
                (uu___116_8917.FStar_TypeChecker_Env.synth);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___116_8917.FStar_TypeChecker_Env.is_native_tactic)
            } in
          let uu____8918 =
            let uu____8924 =
              let uu____8925 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____8925 FStar_Pervasives_Native.fst in
            check_let_bound_def false uu____8924 lb in
          (match uu____8918 with
           | (e1,uu____8937,c1,g1,annotated) ->
               let x =
                 let uu___117_8942 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___117_8942.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___117_8942.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____8943 =
                 let uu____8946 =
                   let uu____8947 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____8947] in
                 FStar_Syntax_Subst.open_term uu____8946 e2 in
               (match uu____8943 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = FStar_Pervasives_Native.fst xbinder in
                    let uu____8959 =
                      let uu____8963 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____8963 e21 in
                    (match uu____8959 with
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
                           let uu____8978 =
                             let uu____8981 =
                               let uu____8982 =
                                 let uu____8990 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____8990) in
                               FStar_Syntax_Syntax.Tm_let uu____8982 in
                             FStar_Syntax_Syntax.mk uu____8981 in
                           uu____8978
                             (FStar_Pervasives_Native.Some
                                ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____9005 =
                             let uu____9006 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____9007 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____9006
                               c1.FStar_Syntax_Syntax.res_typ uu____9007 e11 in
                           FStar_All.pipe_left
                             (fun _0_41  ->
                                FStar_TypeChecker_Common.NonTrivial _0_41)
                             uu____9005 in
                         let g21 =
                           let uu____9009 =
                             let uu____9010 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____9010 g2 in
                           FStar_TypeChecker_Rel.close_guard env2 xb
                             uu____9009 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____9012 =
                           let uu____9013 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____9013 in
                         if uu____9012
                         then
                           let tt =
                             let uu____9019 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____9019 FStar_Option.get in
                           ((let uu____9023 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____9023
                             then
                               let uu____9024 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____9025 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____9024 uu____9025
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape FStar_Pervasives_Native.None
                                env2 [x1] cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____9030 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____9030
                             then
                               let uu____9031 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____9032 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____9031 uu____9032
                             else ());
                            (e4,
                              ((let uu___118_9035 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___118_9035.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___118_9035.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___118_9035.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____9036 -> failwith "Impossible"
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
          let uu____9057 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____9057 with
           | (lbs1,e21) ->
               let uu____9068 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____9068 with
                | (env0,topt) ->
                    let uu____9079 = build_let_rec_env true env0 lbs1 in
                    (match uu____9079 with
                     | (lbs2,rec_env) ->
                         let uu____9090 = check_let_recs rec_env lbs2 in
                         (match uu____9090 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____9102 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____9102
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____9106 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____9106
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
                                     let uu____9134 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____9158 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____9158))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____9134 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____9183  ->
                                           match uu____9183 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____9208 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____9208 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (FStar_Pervasives_Native.Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____9217 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                                match uu____9217 with
                                | (lbs5,e22) ->
                                    ((let uu____9229 =
                                        FStar_TypeChecker_Rel.discharge_guard
                                          env1 g_lbs1 in
                                      FStar_All.pipe_right uu____9229
                                        (FStar_TypeChecker_Rel.force_trivial_guard
                                           env1));
                                     (let uu____9230 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs5), e22))
                                          (FStar_Pervasives_Native.Some
                                             (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                          top.FStar_Syntax_Syntax.pos in
                                      (uu____9230, cres,
                                        FStar_TypeChecker_Rel.trivial_guard)))))))))
      | uu____9243 -> failwith "Impossible"
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
          let uu____9264 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____9264 with
           | (lbs1,e21) ->
               let uu____9275 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____9275 with
                | (env0,topt) ->
                    let uu____9286 = build_let_rec_env false env0 lbs1 in
                    (match uu____9286 with
                     | (lbs2,rec_env) ->
                         let uu____9297 = check_let_recs rec_env lbs2 in
                         (match uu____9297 with
                          | (lbs3,g_lbs) ->
                              let uu____9308 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___119_9324 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___119_9324.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___119_9324.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___120_9326 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___120_9326.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___120_9326.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___120_9326.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___120_9326.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____9308 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____9344 = tc_term env2 e21 in
                                   (match uu____9344 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____9355 =
                                            let uu____9356 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              env2 uu____9356 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____9355 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___121_9360 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___121_9360.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___121_9360.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___121_9360.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____9361 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____9361 with
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
                                                  uu____9386 ->
                                                  (e, cres2, guard)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let tres1 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres in
                                                  let cres3 =
                                                    let uu___122_9391 = cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___122_9391.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___122_9391.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___122_9391.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____9394 -> failwith "Impossible"
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
          let uu____9417 =
            let uu____9420 =
              let uu____9421 = FStar_Syntax_Subst.compress t in
              uu____9421.FStar_Syntax_Syntax.n in
            let uu____9424 =
              let uu____9425 = FStar_Syntax_Subst.compress lbdef in
              uu____9425.FStar_Syntax_Syntax.n in
            (uu____9420, uu____9424) in
          match uu____9417 with
          | (FStar_Syntax_Syntax.Tm_arrow
             (formals,c),FStar_Syntax_Syntax.Tm_abs
             (actuals,uu____9431,uu____9432)) ->
              let actuals1 =
                let uu____9456 =
                  FStar_TypeChecker_Env.set_expected_typ env lbtyp in
                FStar_TypeChecker_Util.maybe_add_implicit_binders uu____9456
                  actuals in
              (if (FStar_List.length formals) <> (FStar_List.length actuals1)
               then
                 (let actuals_msg =
                    let n1 = FStar_List.length actuals1 in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument was found"
                    else
                      (let uu____9481 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments were found"
                         uu____9481) in
                  let formals_msg =
                    let n1 = FStar_List.length formals in
                    if n1 = (Prims.parse_int "1")
                    then "1 argument"
                    else
                      (let uu____9499 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s arguments" uu____9499) in
                  let msg =
                    let uu____9507 = FStar_Syntax_Print.term_to_string lbtyp in
                    let uu____9508 =
                      FStar_Syntax_Print.lbname_to_string lbname in
                    FStar_Util.format4
                      "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                      uu____9507 uu____9508 formals_msg actuals_msg in
                  raise
                    (FStar_Errors.Error
                       (msg, (lbdef.FStar_Syntax_Syntax.pos))))
               else ();
               (let quals =
                  FStar_TypeChecker_Env.lookup_effect_quals env
                    (FStar_Syntax_Util.comp_effect_name c) in
                FStar_All.pipe_right quals
                  (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
          | uu____9513 ->
              let uu____9516 =
                let uu____9517 =
                  let uu____9520 =
                    let uu____9521 = FStar_Syntax_Print.term_to_string lbdef in
                    let uu____9522 = FStar_Syntax_Print.term_to_string lbtyp in
                    FStar_Util.format2
                      "Only function literals with arrow types can be defined recursively; got %s : %s"
                      uu____9521 uu____9522 in
                  (uu____9520, (lbtyp.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____9517 in
              raise uu____9516 in
        let uu____9523 =
          FStar_List.fold_left
            (fun uu____9543  ->
               fun lb  ->
                 match uu____9543 with
                 | (lbs1,env1) ->
                     let uu____9555 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____9555 with
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
                              (let uu____9569 =
                                 let uu____9573 =
                                   let uu____9574 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____9574 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___123_9581 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___123_9581.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___123_9581.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___123_9581.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___123_9581.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___123_9581.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___123_9581.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___123_9581.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___123_9581.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___123_9581.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___123_9581.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___123_9581.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___123_9581.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___123_9581.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___123_9581.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___123_9581.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___123_9581.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___123_9581.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___123_9581.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___123_9581.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___123_9581.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___123_9581.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___123_9581.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___123_9581.FStar_TypeChecker_Env.qname_and_index);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___123_9581.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth =
                                        (uu___123_9581.FStar_TypeChecker_Env.synth);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___123_9581.FStar_TypeChecker_Env.is_native_tactic)
                                    }) t uu____9573 in
                               match uu____9569 with
                               | (t1,uu____9583,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____9587 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left
                                       FStar_Pervasives.ignore uu____9587);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____9589 =
                              (termination_check_enabled
                                 lb.FStar_Syntax_Syntax.lbname e t1)
                                && (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____9589
                            then
                              let uu___124_9590 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___124_9590.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___124_9590.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___124_9590.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___124_9590.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___124_9590.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___124_9590.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___124_9590.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___124_9590.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___124_9590.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___124_9590.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___124_9590.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___124_9590.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___124_9590.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___124_9590.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___124_9590.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___124_9590.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___124_9590.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___124_9590.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___124_9590.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___124_9590.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___124_9590.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___124_9590.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___124_9590.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___124_9590.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___124_9590.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___124_9590.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname
                                (univ_vars1, t1) in
                          let lb1 =
                            let uu___125_9599 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___125_9599.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___125_9599.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____9523 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lbs  ->
      let uu____9613 =
        let uu____9618 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  (let uu____9638 =
                     let uu____9639 =
                       FStar_Syntax_Subst.compress
                         lb.FStar_Syntax_Syntax.lbdef in
                     uu____9639.FStar_Syntax_Syntax.n in
                   match uu____9638 with
                   | FStar_Syntax_Syntax.Tm_abs uu____9642 -> ()
                   | uu____9652 ->
                       let uu____9653 =
                         let uu____9654 =
                           let uu____9657 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname in
                           ("Only function literals may be defined recursively",
                             uu____9657) in
                         FStar_Errors.Error uu____9654 in
                       raise uu____9653);
                  (let uu____9658 =
                     let uu____9662 =
                       FStar_TypeChecker_Env.set_expected_typ env
                         lb.FStar_Syntax_Syntax.lbtyp in
                     tc_tot_or_gtot_term uu____9662
                       lb.FStar_Syntax_Syntax.lbdef in
                   match uu____9658 with
                   | (e,c,g) ->
                       ((let uu____9669 =
                           let uu____9670 =
                             FStar_Syntax_Util.is_total_lcomp c in
                           Prims.op_Negation uu____9670 in
                         if uu____9669
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
        FStar_All.pipe_right uu____9618 FStar_List.unzip in
      match uu____9613 with
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
        let uu____9699 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____9699 with
        | (env1,uu____9709) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____9715 = check_lbtyp top_level env lb in
            (match uu____9715 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____9742 =
                     tc_maybe_toplevel_term
                       (let uu___126_9748 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___126_9748.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___126_9748.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___126_9748.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___126_9748.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___126_9748.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___126_9748.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___126_9748.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___126_9748.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___126_9748.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___126_9748.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___126_9748.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___126_9748.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___126_9748.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___126_9748.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___126_9748.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___126_9748.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___126_9748.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___126_9748.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___126_9748.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___126_9748.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___126_9748.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___126_9748.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___126_9748.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___126_9748.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___126_9748.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___126_9748.FStar_TypeChecker_Env.is_native_tactic)
                        }) e11 in
                   match uu____9742 with
                   | (e12,c1,g1) ->
                       let uu____9757 =
                         let uu____9760 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____9764  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____9760 e12 c1 wf_annot in
                       (match uu____9757 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____9774 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____9774
                              then
                                let uu____9775 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____9776 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____9777 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____9775 uu____9776 uu____9777
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
        | uu____9803 ->
            let uu____9804 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____9804 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____9831 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Rel.trivial_guard, univ_vars1,
                     univ_opening, uu____9831)
                 else
                   (let uu____9836 = FStar_Syntax_Util.type_u () in
                    match uu____9836 with
                    | (k,uu____9847) ->
                        let uu____9848 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____9848 with
                         | (t2,uu____9860,g) ->
                             ((let uu____9863 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____9863
                               then
                                 let uu____9864 =
                                   let uu____9865 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____9865 in
                                 let uu____9866 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____9864 uu____9866
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____9869 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____9869))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 ->
      ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.universe) FStar_Pervasives_Native.tuple4
  =
  fun env  ->
    fun uu____9874  ->
      match uu____9874 with
      | (x,imp) ->
          let uu____9885 = FStar_Syntax_Util.type_u () in
          (match uu____9885 with
           | (tu,u) ->
               ((let uu____9897 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____9897
                 then
                   let uu____9898 = FStar_Syntax_Print.bv_to_string x in
                   let uu____9899 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____9900 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____9898 uu____9899 uu____9900
                 else ());
                (let uu____9902 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____9902 with
                 | (t,uu____9913,g) ->
                     let x1 =
                       ((let uu___127_9919 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___127_9919.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___127_9919.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____9921 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____9921
                       then
                         let uu____9922 =
                           FStar_Syntax_Print.bv_to_string
                             (FStar_Pervasives_Native.fst x1) in
                         let uu____9923 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____9922 uu____9923
                       else ());
                      (let uu____9925 = push_binding env x1 in
                       (x1, uu____9925, g, u))))))
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
            let uu____9976 = tc_binder env1 b in
            (match uu____9976 with
             | (b1,env',g,u) ->
                 let uu____9999 = aux env' bs2 in
                 (match uu____9999 with
                  | (bs3,env'1,g',us) ->
                      let uu____10028 =
                        let uu____10029 =
                          FStar_TypeChecker_Rel.close_guard_univs [u] [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____10029 in
                      ((b1 :: bs3), env'1, uu____10028, (u :: us)))) in
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
          (fun uu____10083  ->
             fun uu____10084  ->
               match (uu____10083, uu____10084) with
               | ((t,imp),(args1,g)) ->
                   let uu____10121 = tc_term env1 t in
                   (match uu____10121 with
                    | (t1,uu____10131,g') ->
                        let uu____10133 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____10133))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____10159  ->
             match uu____10159 with
             | (pats1,g) ->
                 let uu____10173 = tc_args env p in
                 (match uu____10173 with
                  | (args,g') ->
                      let uu____10181 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____10181))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let uu____10189 = tc_maybe_toplevel_term env e in
      match uu____10189 with
      | (e1,c,g) ->
          let uu____10199 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____10199
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____10209 =
               let uu____10212 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____10212
               then
                 let uu____10215 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____10215, false)
               else
                 (let uu____10217 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____10217, true)) in
             match uu____10209 with
             | (target_comp,allow_ghost) ->
                 let uu____10223 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____10223 with
                  | FStar_Pervasives_Native.Some g' ->
                      let uu____10229 =
                        FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____10229)
                  | uu____10230 ->
                      if allow_ghost
                      then
                        let uu____10235 =
                          let uu____10236 =
                            let uu____10239 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____10239, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____10236 in
                        raise uu____10235
                      else
                        (let uu____10244 =
                           let uu____10245 =
                             let uu____10248 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____10248, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____10245 in
                         raise uu____10244)))
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
      let uu____10261 = tc_tot_or_gtot_term env t in
      match uu____10261 with
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
      (let uu____10283 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____10283
       then
         let uu____10284 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____10284
       else ());
      (let env1 =
         let uu___128_10287 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___128_10287.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___128_10287.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___128_10287.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___128_10287.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___128_10287.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___128_10287.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___128_10287.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___128_10287.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___128_10287.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___128_10287.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___128_10287.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___128_10287.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___128_10287.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___128_10287.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___128_10287.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___128_10287.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___128_10287.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___128_10287.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___128_10287.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___128_10287.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___128_10287.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___128_10287.FStar_TypeChecker_Env.qname_and_index);
           FStar_TypeChecker_Env.proof_ns =
             (uu___128_10287.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth =
             (uu___128_10287.FStar_TypeChecker_Env.synth);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___128_10287.FStar_TypeChecker_Env.is_native_tactic)
         } in
       let uu____10290 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____10311) ->
             let uu____10312 =
               let uu____10313 =
                 let uu____10316 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____10316) in
               FStar_Errors.Error uu____10313 in
             raise uu____10312 in
       match uu____10290 with
       | (t,c,g) ->
           let uu____10326 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____10326
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____10333 =
                let uu____10334 =
                  let uu____10337 =
                    let uu____10338 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____10338 in
                  let uu____10339 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____10337, uu____10339) in
                FStar_Errors.Error uu____10334 in
              raise uu____10333))
let level_of_type_fail env e t =
  let uu____10364 =
    let uu____10365 =
      let uu____10368 =
        let uu____10369 = FStar_Syntax_Print.term_to_string e in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____10369 t in
      let uu____10370 = FStar_TypeChecker_Env.get_range env in
      (uu____10368, uu____10370) in
    FStar_Errors.Error uu____10365 in
  raise uu____10364
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____10390 =
            let uu____10391 = FStar_Syntax_Util.unrefine t1 in
            uu____10391.FStar_Syntax_Syntax.n in
          match uu____10390 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____10395 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____10398 = FStar_Syntax_Util.type_u () in
                 match uu____10398 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___131_10404 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___131_10404.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___131_10404.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___131_10404.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___131_10404.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___131_10404.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___131_10404.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___131_10404.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___131_10404.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___131_10404.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___131_10404.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___131_10404.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___131_10404.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___131_10404.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___131_10404.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___131_10404.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___131_10404.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___131_10404.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___131_10404.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___131_10404.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___131_10404.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___131_10404.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___131_10404.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___131_10404.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___131_10404.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___131_10404.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___131_10404.FStar_TypeChecker_Env.is_native_tactic)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____10408 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____10408
                       | uu____10409 ->
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
      let uu____10420 =
        let uu____10421 = FStar_Syntax_Subst.compress e in
        uu____10421.FStar_Syntax_Syntax.n in
      match uu____10420 with
      | FStar_Syntax_Syntax.Tm_bvar uu____10426 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____10431 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____10448 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____10459) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____10474,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____10493) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10500 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10500 with | ((uu____10507,t),uu____10509) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10512,(FStar_Util.Inl t,uu____10514),uu____10515) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____10551,(FStar_Util.Inr c,uu____10553),uu____10554) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____10597;
             FStar_Syntax_Syntax.pos = uu____10598;
             FStar_Syntax_Syntax.vars = uu____10599;_},us)
          ->
          let uu____10605 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____10605 with
           | ((us',t),uu____10614) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____10626 =
                     let uu____10627 =
                       let uu____10630 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____10630) in
                     FStar_Errors.Error uu____10627 in
                   raise uu____10626)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10642 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____10643 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____10651) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____10668 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____10668 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____10683  ->
                      match uu____10683 with
                      | (b,uu____10687) ->
                          let uu____10688 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____10688) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____10693 = universe_of_aux env res in
                 level_of_type env res uu____10693 in
               let u_c =
                 let uu____10695 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____10695 with
                 | FStar_Pervasives_Native.None  -> u_res
                 | FStar_Pervasives_Native.Some trepr ->
                     let uu____10698 = universe_of_aux env trepr in
                     level_of_type env trepr uu____10698 in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____10768 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____10778 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____10802 ->
                let uu____10803 = universe_of_aux env hd3 in
                (uu____10803, args1)
            | FStar_Syntax_Syntax.Tm_name uu____10813 ->
                let uu____10814 = universe_of_aux env hd3 in
                (uu____10814, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____10824 ->
                let uu____10835 = universe_of_aux env hd3 in
                (uu____10835, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____10845 ->
                let uu____10850 = universe_of_aux env hd3 in
                (uu____10850, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____10860 ->
                let uu____10878 = universe_of_aux env hd3 in
                (uu____10878, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____10888 ->
                let uu____10893 = universe_of_aux env hd3 in
                (uu____10893, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____10903 ->
                let uu____10904 = universe_of_aux env hd3 in
                (uu____10904, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____10914 ->
                let uu____10922 = universe_of_aux env hd3 in
                (uu____10922, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____10932 ->
                let uu____10937 = universe_of_aux env hd3 in
                (uu____10937, args1)
            | FStar_Syntax_Syntax.Tm_type uu____10947 ->
                let uu____10948 = universe_of_aux env hd3 in
                (uu____10948, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____10958,hd4::uu____10960) ->
                let uu____11003 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____11003 with
                 | (uu____11013,uu____11014,hd5) ->
                     let uu____11028 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____11028 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____11063 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____11065 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____11065 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____11100 ->
                let uu____11101 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____11101 with
                 | (env1,uu____11115) ->
                     let env2 =
                       let uu___132_11119 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___132_11119.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___132_11119.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___132_11119.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___132_11119.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___132_11119.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___132_11119.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___132_11119.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___132_11119.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___132_11119.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___132_11119.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___132_11119.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___132_11119.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___132_11119.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___132_11119.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___132_11119.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___132_11119.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___132_11119.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___132_11119.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___132_11119.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___132_11119.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___132_11119.FStar_TypeChecker_Env.qname_and_index);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___132_11119.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth =
                           (uu___132_11119.FStar_TypeChecker_Env.synth);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___132_11119.FStar_TypeChecker_Env.is_native_tactic)
                       } in
                     ((let uu____11121 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____11121
                       then
                         let uu____11122 =
                           let uu____11123 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____11123 in
                         let uu____11124 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____11122 uu____11124
                       else ());
                      (let uu____11126 = tc_term env2 hd3 in
                       match uu____11126 with
                       | (uu____11139,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____11140;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____11142;
                                        FStar_Syntax_Syntax.comp =
                                          uu____11143;_},g)
                           ->
                           ((let uu____11153 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____11153
                               FStar_Pervasives.ignore);
                            (t, args1))))) in
          let uu____11161 = type_of_head true hd1 args in
          (match uu____11161 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____11190 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____11190 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____11227 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____11227)))
      | FStar_Syntax_Syntax.Tm_match (uu____11230,hd1::uu____11232) ->
          let uu____11275 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____11275 with
           | (uu____11278,uu____11279,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____11293,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____11327 = universe_of_aux env e in
      level_of_type env e uu____11327
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.universes)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun tps  ->
      let uu____11342 = tc_binders env tps in
      match uu____11342 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))