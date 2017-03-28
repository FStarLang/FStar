open Prims
let instantiate_both: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    let uu___86_4 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___86_4.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___86_4.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___86_4.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___86_4.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___86_4.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___86_4.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___86_4.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___86_4.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___86_4.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___86_4.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___86_4.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___86_4.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___86_4.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___86_4.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___86_4.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___86_4.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___86_4.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___86_4.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___86_4.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___86_4.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___86_4.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___86_4.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___86_4.FStar_TypeChecker_Env.qname_and_index)
    }
let no_inst: FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env =
  fun env  ->
    let uu___87_8 = env in
    {
      FStar_TypeChecker_Env.solver = (uu___87_8.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___87_8.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___87_8.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___87_8.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___87_8.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___87_8.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___87_8.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___87_8.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___87_8.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___87_8.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___87_8.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___87_8.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___87_8.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___87_8.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___87_8.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___87_8.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___87_8.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___87_8.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___87_8.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.type_of =
        (uu___87_8.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___87_8.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___87_8.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qname_and_index =
        (uu___87_8.FStar_TypeChecker_Env.qname_and_index)
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
           let uu____34 =
             let uu____35 =
               let uu____36 = FStar_Syntax_Syntax.as_arg v1 in
               let uu____37 =
                 let uu____39 = FStar_Syntax_Syntax.as_arg tl1 in [uu____39] in
               uu____36 :: uu____37 in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____35 in
           uu____34 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)
      vs FStar_Syntax_Util.lex_top
let is_eq: FStar_Syntax_Syntax.arg_qualifier Prims.option -> Prims.bool =
  fun uu___80_47  ->
    match uu___80_47 with
    | Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____49 -> false
let steps env =
  [FStar_TypeChecker_Normalize.Beta;
  FStar_TypeChecker_Normalize.Eager_unfolding]
let unfold_whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.WHNF;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Beta] env t
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
  FStar_Syntax_Syntax.term Prims.option ->
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
            | uu____100 ->
                let t1 = if try_norm then norm env t else t in
                let fvs' = FStar_Syntax_Free.names t1 in
                let uu____106 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs in
                (match uu____106 with
                 | None  -> t1
                 | Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail uu____114 =
                          let msg =
                            match head_opt with
                            | None  ->
                                let uu____116 =
                                  FStar_Syntax_Print.bv_to_string x in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____116
                            | Some head1 ->
                                let uu____118 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____119 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1 in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____118 uu____119 in
                          let uu____120 =
                            let uu____121 =
                              let uu____124 =
                                FStar_TypeChecker_Env.get_range env in
                              (msg, uu____124) in
                            FStar_Errors.Error uu____121 in
                          Prims.raise uu____120 in
                        let s =
                          let uu____126 =
                            let uu____127 = FStar_Syntax_Util.type_u () in
                            FStar_All.pipe_left Prims.fst uu____127 in
                          FStar_TypeChecker_Util.new_uvar env uu____126 in
                        let uu____132 =
                          FStar_TypeChecker_Rel.try_teq env t1 s in
                        match uu____132 with
                        | Some g ->
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             s)
                        | uu____136 -> fail ())) in
          aux false kt
let push_binding env b = FStar_TypeChecker_Env.push_bv env (Prims.fst b)
let maybe_extend_subst:
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.binder ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.subst_t
  =
  fun s  ->
    fun b  ->
      fun v1  ->
        let uu____167 = FStar_Syntax_Syntax.is_null_binder b in
        if uu____167
        then s
        else (FStar_Syntax_Syntax.NT ((Prims.fst b), v1)) :: s
let set_lcomp_result:
  FStar_Syntax_Syntax.lcomp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.lcomp
  =
  fun lc  ->
    fun t  ->
      let uu___88_181 = lc in
      {
        FStar_Syntax_Syntax.eff_name =
          (uu___88_181.FStar_Syntax_Syntax.eff_name);
        FStar_Syntax_Syntax.res_typ = t;
        FStar_Syntax_Syntax.cflags = (uu___88_181.FStar_Syntax_Syntax.cflags);
        FStar_Syntax_Syntax.comp =
          (fun uu____182  ->
             let uu____183 = lc.FStar_Syntax_Syntax.comp () in
             FStar_Syntax_Util.set_result_typ uu____183 t)
      }
let memo_tk:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun e  ->
    fun t  ->
      FStar_ST.write e.FStar_Syntax_Syntax.tk
        (Some (t.FStar_Syntax_Syntax.n));
      e
let value_check_expected_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp) FStar_Util.either
        ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
            FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun tlc  ->
        fun guard  ->
          let should_return t =
            let uu____222 =
              let uu____223 = FStar_Syntax_Subst.compress t in
              uu____223.FStar_Syntax_Syntax.n in
            match uu____222 with
            | FStar_Syntax_Syntax.Tm_arrow (uu____226,c) ->
                let uu____238 =
                  FStar_TypeChecker_Util.is_pure_or_ghost_effect env
                    (FStar_Syntax_Util.comp_effect_name c) in
                if uu____238
                then
                  let t1 =
                    FStar_All.pipe_left FStar_Syntax_Util.unrefine
                      (FStar_Syntax_Util.comp_result c) in
                  let uu____240 =
                    let uu____241 = FStar_Syntax_Subst.compress t1 in
                    uu____241.FStar_Syntax_Syntax.n in
                  (match uu____240 with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.unit_lid
                       -> false
                   | FStar_Syntax_Syntax.Tm_constant uu____245 -> false
                   | uu____246 -> true)
                else false
            | uu____248 -> true in
          let lc =
            match tlc with
            | FStar_Util.Inl t ->
                let uu____251 =
                  let uu____254 =
                    (let uu____255 = should_return t in
                     Prims.op_Negation uu____255) ||
                      (let uu____256 =
                         FStar_TypeChecker_Env.should_verify env in
                       Prims.op_Negation uu____256) in
                  if uu____254
                  then FStar_Syntax_Syntax.mk_Total t
                  else FStar_TypeChecker_Util.return_value env t e in
                FStar_Syntax_Util.lcomp_of_comp uu____251
            | FStar_Util.Inr lc -> lc in
          let t = lc.FStar_Syntax_Syntax.res_typ in
          let uu____264 =
            let uu____268 = FStar_TypeChecker_Env.expected_typ env in
            match uu____268 with
            | None  -> let uu____273 = memo_tk e t in (uu____273, lc, guard)
            | Some t' ->
                ((let uu____276 =
                    FStar_TypeChecker_Env.debug env FStar_Options.High in
                  if uu____276
                  then
                    let uu____277 = FStar_Syntax_Print.term_to_string t in
                    let uu____278 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2
                      "Computed return type %s; expected type %s\n" uu____277
                      uu____278
                  else ());
                 (let uu____280 =
                    FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                      t' in
                  match uu____280 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_Syntax_Syntax.res_typ in
                      let uu____291 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t' in
                      (match uu____291 with
                       | (e2,g) ->
                           ((let uu____300 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High in
                             if uu____300
                             then
                               let uu____301 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____302 =
                                 FStar_Syntax_Print.term_to_string t' in
                               let uu____303 =
                                 FStar_TypeChecker_Rel.guard_to_string env g in
                               let uu____304 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____301 uu____302 uu____303 uu____304
                             else ());
                            (let msg =
                               let uu____310 =
                                 FStar_TypeChecker_Rel.is_trivial g in
                               if uu____310
                               then None
                               else
                                 FStar_All.pipe_left
                                   (fun _0_28  -> Some _0_28)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t') in
                             let g1 =
                               FStar_TypeChecker_Rel.conj_guard g guard in
                             let uu____325 =
                               FStar_TypeChecker_Util.strengthen_precondition
                                 msg env e2 lc1 g1 in
                             match uu____325 with
                             | (lc2,g2) ->
                                 let uu____333 = memo_tk e2 t' in
                                 (uu____333, (set_lcomp_result lc2 t'), g2)))))) in
          match uu____264 with
          | (e1,lc1,g) ->
              ((let uu____341 =
                  FStar_TypeChecker_Env.debug env FStar_Options.Low in
                if uu____341
                then
                  let uu____342 = FStar_Syntax_Print.lcomp_to_string lc1 in
                  FStar_Util.print1 "Return comp type is %s\n" uu____342
                else ());
               (e1, lc1, g))
let comp_check_expected_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
          FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let uu____359 = FStar_TypeChecker_Env.expected_typ env in
        match uu____359 with
        | None  -> (e, lc, FStar_TypeChecker_Rel.trivial_guard)
        | Some t ->
            let uu____365 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t in
            (match uu____365 with
             | (e1,lc1) ->
                 FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
let check_expected_effect:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp Prims.option ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp) ->
        (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.comp*
          FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun copt  ->
      fun uu____387  ->
        match uu____387 with
        | (e,c) ->
            let expected_c_opt =
              match copt with
              | Some uu____402 -> copt
              | None  ->
                  let uu____403 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Syntax_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____404 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c in
                          Prims.op_Negation uu____404)) in
                  if uu____403
                  then
                    let uu____406 =
                      FStar_Syntax_Util.ml_comp
                        (FStar_Syntax_Util.comp_result c)
                        e.FStar_Syntax_Syntax.pos in
                    Some uu____406
                  else
                    (let uu____408 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                     if uu____408
                     then None
                     else
                       (let uu____411 = FStar_Syntax_Util.is_pure_comp c in
                        if uu____411
                        then
                          let uu____413 =
                            FStar_Syntax_Syntax.mk_Total
                              (FStar_Syntax_Util.comp_result c) in
                          Some uu____413
                        else
                          (let uu____415 =
                             FStar_Syntax_Util.is_pure_or_ghost_comp c in
                           if uu____415
                           then
                             let uu____417 =
                               FStar_Syntax_Syntax.mk_GTotal
                                 (FStar_Syntax_Util.comp_result c) in
                             Some uu____417
                           else None))) in
            (match expected_c_opt with
             | None  ->
                 let uu____422 = norm_c env c in
                 (e, uu____422, FStar_TypeChecker_Rel.trivial_guard)
             | Some expected_c ->
                 ((let uu____425 =
                     FStar_TypeChecker_Env.debug env FStar_Options.Low in
                   if uu____425
                   then
                     let uu____426 = FStar_Syntax_Print.term_to_string e in
                     let uu____427 = FStar_Syntax_Print.comp_to_string c in
                     let uu____428 =
                       FStar_Syntax_Print.comp_to_string expected_c in
                     FStar_Util.print3
                       "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                       uu____426 uu____427 uu____428
                   else ());
                  (let c1 = norm_c env c in
                   (let uu____432 =
                      FStar_TypeChecker_Env.debug env FStar_Options.Low in
                    if uu____432
                    then
                      let uu____433 = FStar_Syntax_Print.term_to_string e in
                      let uu____434 = FStar_Syntax_Print.comp_to_string c1 in
                      let uu____435 =
                        FStar_Syntax_Print.comp_to_string expected_c in
                      FStar_Util.print3
                        "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n"
                        uu____433 uu____434 uu____435
                    else ());
                   (let uu____437 =
                      FStar_TypeChecker_Util.check_comp env e c1 expected_c in
                    match uu____437 with
                    | (e1,uu____445,g) ->
                        let g1 =
                          let uu____448 = FStar_TypeChecker_Env.get_range env in
                          FStar_TypeChecker_Util.label_guard uu____448
                            "could not prove post-condition" g in
                        ((let uu____450 =
                            FStar_TypeChecker_Env.debug env FStar_Options.Low in
                          if uu____450
                          then
                            let uu____451 =
                              FStar_Range.string_of_range
                                e1.FStar_Syntax_Syntax.pos in
                            let uu____452 =
                              FStar_TypeChecker_Rel.guard_to_string env g1 in
                            FStar_Util.print2
                              "(%s) DONE check_expected_effect; guard is: %s\n"
                              uu____451 uu____452
                          else ());
                         (let e2 =
                            FStar_TypeChecker_Util.maybe_lift env e1
                              (FStar_Syntax_Util.comp_effect_name c1)
                              (FStar_Syntax_Util.comp_effect_name expected_c)
                              (FStar_Syntax_Util.comp_result c1) in
                          (e2, expected_c, g1)))))))
let no_logical_guard env uu____474 =
  match uu____474 with
  | (te,kt,f) ->
      let uu____481 = FStar_TypeChecker_Rel.guard_form f in
      (match uu____481 with
       | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
       | FStar_TypeChecker_Common.NonTrivial f1 ->
           let uu____486 =
             let uu____487 =
               let uu____490 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1 in
               let uu____491 = FStar_TypeChecker_Env.get_range env in
               (uu____490, uu____491) in
             FStar_Errors.Error uu____487 in
           Prims.raise uu____486)
let print_expected_ty: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let uu____498 = FStar_TypeChecker_Env.expected_typ env in
    match uu____498 with
    | None  -> FStar_Util.print_string "Expected type is None"
    | Some t ->
        let uu____501 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.print1 "Expected type is %s" uu____501
let check_smt_pat env t bs c =
  let uu____536 = FStar_Syntax_Util.is_smt_lemma t in
  if uu____536
  then
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp
        { FStar_Syntax_Syntax.comp_univs = uu____537;
          FStar_Syntax_Syntax.effect_name = uu____538;
          FStar_Syntax_Syntax.result_typ = uu____539;
          FStar_Syntax_Syntax.effect_args = _pre::_post::(pats,uu____543)::[];
          FStar_Syntax_Syntax.flags = uu____544;_}
        ->
        let pat_vars =
          let uu____578 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.Beta] env pats in
          FStar_Syntax_Free.names uu____578 in
        let uu____579 =
          FStar_All.pipe_right bs
            (FStar_Util.find_opt
               (fun uu____591  ->
                  match uu____591 with
                  | (b,uu____595) ->
                      let uu____596 = FStar_Util.set_mem b pat_vars in
                      Prims.op_Negation uu____596)) in
        (match uu____579 with
         | None  -> ()
         | Some (x,uu____600) ->
             let uu____603 =
               let uu____604 = FStar_Syntax_Print.bv_to_string x in
               FStar_Util.format1
                 "Pattern misses at least one bound variable: %s" uu____604 in
             FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____603)
    | uu____605 -> failwith "Impossible"
  else ()
let guard_letrecs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname* FStar_Syntax_Syntax.typ) Prims.list
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        let uu____626 =
          let uu____627 = FStar_TypeChecker_Env.should_verify env in
          Prims.op_Negation uu____627 in
        if uu____626
        then env.FStar_TypeChecker_Env.letrecs
        else
          (match env.FStar_TypeChecker_Env.letrecs with
           | [] -> []
           | letrecs ->
               let r = FStar_TypeChecker_Env.get_range env in
               let env1 =
                 let uu___89_645 = env in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___89_645.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___89_645.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___89_645.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___89_645.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___89_645.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___89_645.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___89_645.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___89_645.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___89_645.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___89_645.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___89_645.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___89_645.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs = [];
                   FStar_TypeChecker_Env.top_level =
                     (uu___89_645.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___89_645.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___89_645.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___89_645.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___89_645.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___89_645.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___89_645.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.type_of =
                     (uu___89_645.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___89_645.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___89_645.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qname_and_index =
                     (uu___89_645.FStar_TypeChecker_Env.qname_and_index)
                 } in
               let precedes =
                 FStar_TypeChecker_Util.fvar_const env1
                   FStar_Syntax_Const.precedes_lid in
               let decreases_clause bs c =
                 let filter_types_and_functions bs1 =
                   FStar_All.pipe_right bs1
                     (FStar_List.collect
                        (fun uu____668  ->
                           match uu____668 with
                           | (b,uu____673) ->
                               let t =
                                 let uu____675 =
                                   FStar_Syntax_Util.unrefine
                                     b.FStar_Syntax_Syntax.sort in
                                 unfold_whnf env1 uu____675 in
                               (match t.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_type _
                                  |FStar_Syntax_Syntax.Tm_arrow _ -> []
                                | uu____679 ->
                                    let uu____680 =
                                      FStar_Syntax_Syntax.bv_to_name b in
                                    [uu____680]))) in
                 let as_lex_list dec =
                   let uu____685 = FStar_Syntax_Util.head_and_args dec in
                   match uu____685 with
                   | (head1,uu____696) ->
                       (match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.lexcons_lid
                            -> dec
                        | uu____712 -> mk_lex_list [dec]) in
                 let cflags = FStar_Syntax_Util.comp_flags c in
                 let uu____715 =
                   FStar_All.pipe_right cflags
                     (FStar_List.tryFind
                        (fun uu___81_719  ->
                           match uu___81_719 with
                           | FStar_Syntax_Syntax.DECREASES uu____720 -> true
                           | uu____723 -> false)) in
                 match uu____715 with
                 | Some (FStar_Syntax_Syntax.DECREASES dec) ->
                     as_lex_list dec
                 | uu____727 ->
                     let xs =
                       FStar_All.pipe_right bs filter_types_and_functions in
                     (match xs with
                      | x::[] -> x
                      | uu____733 -> mk_lex_list xs) in
               let previous_dec = decreases_clause actuals expected_c in
               let guard_one_letrec uu____745 =
                 match uu____745 with
                 | (l,t) ->
                     let uu____754 =
                       let uu____755 = FStar_Syntax_Subst.compress t in
                       uu____755.FStar_Syntax_Syntax.n in
                     (match uu____754 with
                      | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                          let formals1 =
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____788  ->
                                    match uu____788 with
                                    | (x,imp) ->
                                        let uu____795 =
                                          FStar_Syntax_Syntax.is_null_bv x in
                                        if uu____795
                                        then
                                          let uu____798 =
                                            let uu____799 =
                                              let uu____801 =
                                                FStar_Syntax_Syntax.range_of_bv
                                                  x in
                                              Some uu____801 in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____799
                                              x.FStar_Syntax_Syntax.sort in
                                          (uu____798, imp)
                                        else (x, imp))) in
                          let uu____803 =
                            FStar_Syntax_Subst.open_comp formals1 c in
                          (match uu____803 with
                           | (formals2,c1) ->
                               let dec = decreases_clause formals2 c1 in
                               let precedes1 =
                                 let uu____816 =
                                   let uu____817 =
                                     let uu____818 =
                                       FStar_Syntax_Syntax.as_arg dec in
                                     let uu____819 =
                                       let uu____821 =
                                         FStar_Syntax_Syntax.as_arg
                                           previous_dec in
                                       [uu____821] in
                                     uu____818 :: uu____819 in
                                   FStar_Syntax_Syntax.mk_Tm_app precedes
                                     uu____817 in
                                 uu____816 None r in
                               let uu____826 = FStar_Util.prefix formals2 in
                               (match uu____826 with
                                | (bs,(last1,imp)) ->
                                    let last2 =
                                      let uu___90_852 = last1 in
                                      let uu____853 =
                                        FStar_Syntax_Util.refine last1
                                          precedes1 in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___90_852.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___90_852.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____853
                                      } in
                                    let refined_formals =
                                      FStar_List.append bs [(last2, imp)] in
                                    let t' =
                                      FStar_Syntax_Util.arrow refined_formals
                                        c1 in
                                    ((let uu____870 =
                                        FStar_TypeChecker_Env.debug env1
                                          FStar_Options.Low in
                                      if uu____870
                                      then
                                        let uu____871 =
                                          FStar_Syntax_Print.lbname_to_string
                                            l in
                                        let uu____872 =
                                          FStar_Syntax_Print.term_to_string t in
                                        let uu____873 =
                                          FStar_Syntax_Print.term_to_string
                                            t' in
                                        FStar_Util.print3
                                          "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                          uu____871 uu____872 uu____873
                                      else ());
                                     (l, t'))))
                      | uu____877 ->
                          Prims.raise
                            (FStar_Errors.Error
                               ("Annotated type of 'let rec' must be an arrow",
                                 (t.FStar_Syntax_Syntax.pos)))) in
               FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))
let rec tc_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      tc_maybe_toplevel_term
        (let uu___91_1141 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___91_1141.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___91_1141.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___91_1141.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___91_1141.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___91_1141.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___91_1141.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___91_1141.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___91_1141.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___91_1141.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___91_1141.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___91_1141.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___91_1141.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___91_1141.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___91_1141.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___91_1141.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___91_1141.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___91_1141.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___91_1141.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___91_1141.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___91_1141.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___91_1141.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___91_1141.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___91_1141.FStar_TypeChecker_Env.qname_and_index)
         }) e
and tc_maybe_toplevel_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      (let uu____1150 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____1150
       then
         let uu____1151 =
           let uu____1152 = FStar_TypeChecker_Env.get_range env1 in
           FStar_All.pipe_left FStar_Range.string_of_range uu____1152 in
         let uu____1153 = FStar_Syntax_Print.tag_of_term e in
         FStar_Util.print2 "%s (%s)\n" uu____1151 uu____1153
       else ());
      (let top = FStar_Syntax_Subst.compress e in
       match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1159 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst _
         |FStar_Syntax_Syntax.Tm_uvar _
          |FStar_Syntax_Syntax.Tm_bvar _
           |FStar_Syntax_Syntax.Tm_name _
            |FStar_Syntax_Syntax.Tm_fvar _
             |FStar_Syntax_Syntax.Tm_constant _
              |FStar_Syntax_Syntax.Tm_abs _
               |FStar_Syntax_Syntax.Tm_arrow _
                |FStar_Syntax_Syntax.Tm_refine _
                 |FStar_Syntax_Syntax.Tm_type _
                  |FStar_Syntax_Syntax.Tm_unknown 
           -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____1198 = tc_tot_or_gtot_term env1 e1 in
           (match uu____1198 with
            | (e2,c,g) ->
                let g1 =
                  let uu___92_1209 = g in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___92_1209.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___92_1209.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___92_1209.FStar_TypeChecker_Env.implicits)
                  } in
                (e2, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern pats) ->
           let uu____1222 = FStar_Syntax_Util.type_u () in
           (match uu____1222 with
            | (t,u) ->
                let uu____1230 = tc_check_tot_or_gtot_term env1 e1 t in
                (match uu____1230 with
                 | (e2,c,g) ->
                     let uu____1240 =
                       let uu____1249 =
                         FStar_TypeChecker_Env.clear_expected_typ env1 in
                       match uu____1249 with
                       | (env2,uu____1262) -> tc_pats env2 pats in
                     (match uu____1240 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___93_1283 = g' in
                            {
                              FStar_TypeChecker_Env.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Env.deferred =
                                (uu___93_1283.FStar_TypeChecker_Env.deferred);
                              FStar_TypeChecker_Env.univ_ineqs =
                                (uu___93_1283.FStar_TypeChecker_Env.univ_ineqs);
                              FStar_TypeChecker_Env.implicits =
                                (uu___93_1283.FStar_TypeChecker_Env.implicits)
                            } in
                          let uu____1284 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e2,
                                    (FStar_Syntax_Syntax.Meta_pattern pats1))))
                              (Some (t.FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____1295 =
                            FStar_TypeChecker_Rel.conj_guard g g'1 in
                          (uu____1284, c, uu____1295))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____1303 =
             let uu____1304 = FStar_Syntax_Subst.compress e1 in
             uu____1304.FStar_Syntax_Syntax.n in
           (match uu____1303 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____1310,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____1312;
                               FStar_Syntax_Syntax.lbtyp = uu____1313;
                               FStar_Syntax_Syntax.lbeff = uu____1314;
                               FStar_Syntax_Syntax.lbdef = e11;_}::[]),e2)
                ->
                let uu____1332 =
                  let uu____1336 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_TypeChecker_Common.t_unit in
                  tc_term uu____1336 e11 in
                (match uu____1332 with
                 | (e12,c1,g1) ->
                     let uu____1343 = tc_term env1 e2 in
                     (match uu____1343 with
                      | (e21,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.bind
                              e12.FStar_Syntax_Syntax.pos env1 (Some e12) c1
                              (None, c2) in
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
                            let uu____1360 =
                              let uu____1363 =
                                let uu____1364 =
                                  let uu____1372 =
                                    let uu____1376 =
                                      let uu____1378 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_Syntax_Syntax.eff_name),
                                            FStar_TypeChecker_Common.t_unit,
                                            e13) in
                                      [uu____1378] in
                                    (false, uu____1376) in
                                  (uu____1372, e22) in
                                FStar_Syntax_Syntax.Tm_let uu____1364 in
                              FStar_Syntax_Syntax.mk uu____1363 in
                            uu____1360
                              (Some
                                 ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                              e1.FStar_Syntax_Syntax.pos in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env1 e3
                              c.FStar_Syntax_Syntax.eff_name
                              c.FStar_Syntax_Syntax.res_typ in
                          let e5 =
                            (FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (e4,
                                    (FStar_Syntax_Syntax.Meta_desugared
                                       FStar_Syntax_Syntax.Sequence))))
                              (Some
                                 ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                              top.FStar_Syntax_Syntax.pos in
                          let uu____1408 =
                            FStar_TypeChecker_Rel.conj_guard g1 g2 in
                          (e5, c, uu____1408)))
            | uu____1411 ->
                let uu____1412 = tc_term env1 e1 in
                (match uu____1412 with
                 | (e2,c,g) ->
                     let e3 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (e2,
                               (FStar_Syntax_Syntax.Meta_desugared
                                  FStar_Syntax_Syntax.Sequence))))
                         (Some
                            ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                         top.FStar_Syntax_Syntax.pos in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____1436) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____1451 = tc_term env1 e1 in
           (match uu____1451 with
            | (e2,c,g) ->
                let e3 =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_meta (e2, m)))
                    (Some
                       ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                    top.FStar_Syntax_Syntax.pos in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,FStar_Util.Inr expected_c,uu____1476) ->
           let uu____1495 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____1495 with
            | (env0,uu____1503) ->
                let uu____1506 = tc_comp env0 expected_c in
                (match uu____1506 with
                 | (expected_c1,uu____1514,g) ->
                     let t_res = FStar_Syntax_Util.comp_result expected_c1 in
                     let uu____1519 =
                       let uu____1523 =
                         FStar_TypeChecker_Env.set_expected_typ env0 t_res in
                       tc_term uu____1523 e1 in
                     (match uu____1519 with
                      | (e2,c',g') ->
                          let uu____1530 =
                            let uu____1534 =
                              let uu____1537 = c'.FStar_Syntax_Syntax.comp () in
                              (e2, uu____1537) in
                            check_expected_effect env0 (Some expected_c1)
                              uu____1534 in
                          (match uu____1530 with
                           | (e3,expected_c2,g'') ->
                               let e4 =
                                 (FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_ascribed
                                       (e3, (FStar_Util.Inl t_res),
                                         (Some
                                            (FStar_Syntax_Util.comp_effect_name
                                               expected_c2)))))
                                   (Some (t_res.FStar_Syntax_Syntax.n))
                                   top.FStar_Syntax_Syntax.pos in
                               let lc =
                                 FStar_Syntax_Util.lcomp_of_comp expected_c2 in
                               let f =
                                 let uu____1572 =
                                   FStar_TypeChecker_Rel.conj_guard g' g'' in
                                 FStar_TypeChecker_Rel.conj_guard g
                                   uu____1572 in
                               let uu____1573 =
                                 comp_check_expected_typ env1 e4 lc in
                               (match uu____1573 with
                                | (e5,c,f2) ->
                                    let uu____1583 =
                                      FStar_TypeChecker_Rel.conj_guard f f2 in
                                    (e5, c, uu____1583))))))
       | FStar_Syntax_Syntax.Tm_ascribed (e1,FStar_Util.Inl t,uu____1586) ->
           let uu____1605 = FStar_Syntax_Util.type_u () in
           (match uu____1605 with
            | (k,u) ->
                let uu____1613 = tc_check_tot_or_gtot_term env1 t k in
                (match uu____1613 with
                 | (t1,uu____1621,f) ->
                     let uu____1623 =
                       let uu____1627 =
                         FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                       tc_term uu____1627 e1 in
                     (match uu____1623 with
                      | (e2,c,g) ->
                          let uu____1634 =
                            let uu____1637 =
                              FStar_TypeChecker_Env.set_range env1
                                t1.FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Util.strengthen_precondition
                              (Some
                                 (fun uu____1640  ->
                                    FStar_TypeChecker_Err.ill_kinded_type))
                              uu____1637 e2 c f in
                          (match uu____1634 with
                           | (c1,f1) ->
                               let uu____1646 =
                                 let uu____1650 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e2, (FStar_Util.Inl t1),
                                           (Some
                                              (c1.FStar_Syntax_Syntax.eff_name)))))
                                     (Some (t1.FStar_Syntax_Syntax.n))
                                     top.FStar_Syntax_Syntax.pos in
                                 comp_check_expected_typ env1 uu____1650 c1 in
                               (match uu____1646 with
                                | (e3,c2,f2) ->
                                    let uu____1672 =
                                      let uu____1673 =
                                        FStar_TypeChecker_Rel.conj_guard g f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____1673 in
                                    (e3, c2, uu____1672))))))
       | FStar_Syntax_Syntax.Tm_app
         ({
            FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
              (FStar_Const.Const_reify );
            FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
            FStar_Syntax_Syntax.vars = _;_},a::hd1::rest)
         |FStar_Syntax_Syntax.Tm_app
         ({
            FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
              (FStar_Const.Const_reflect _);
            FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
            FStar_Syntax_Syntax.vars = _;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest in
           let uu____1750 = FStar_Syntax_Util.head_and_args top in
           (match uu____1750 with
            | (unary_op,uu____1764) ->
                let head1 =
                  let uu____1782 =
                    FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos
                      (Prims.fst a).FStar_Syntax_Syntax.pos in
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))) None
                    uu____1782 in
                let t =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (head1, rest1))) None
                    top.FStar_Syntax_Syntax.pos in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.tk = uu____1826;
              FStar_Syntax_Syntax.pos = uu____1827;
              FStar_Syntax_Syntax.vars = uu____1828;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reify is irrelevant and will be ignored"
            else ();
            (let uu____1854 =
               let uu____1858 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               match uu____1858 with | (env0,uu____1866) -> tc_term env0 e1 in
             match uu____1854 with
             | (e2,c,g) ->
                 let uu____1875 = FStar_Syntax_Util.head_and_args top in
                 (match uu____1875 with
                  | (reify_op,uu____1889) ->
                      let u_c =
                        let uu____1905 =
                          tc_term env1 c.FStar_Syntax_Syntax.res_typ in
                        match uu____1905 with
                        | (uu____1909,c',uu____1911) ->
                            let uu____1912 =
                              let uu____1913 =
                                FStar_Syntax_Subst.compress
                                  c'.FStar_Syntax_Syntax.res_typ in
                              uu____1913.FStar_Syntax_Syntax.n in
                            (match uu____1912 with
                             | FStar_Syntax_Syntax.Tm_type u -> u
                             | uu____1917 ->
                                 let uu____1918 = FStar_Syntax_Util.type_u () in
                                 (match uu____1918 with
                                  | (t,u) ->
                                      let g_opt =
                                        FStar_TypeChecker_Rel.try_teq env1
                                          c'.FStar_Syntax_Syntax.res_typ t in
                                      ((match g_opt with
                                        | Some g' ->
                                            FStar_TypeChecker_Rel.force_trivial_guard
                                              env1 g'
                                        | None  ->
                                            let uu____1927 =
                                              let uu____1928 =
                                                FStar_Syntax_Print.lcomp_to_string
                                                  c' in
                                              let uu____1929 =
                                                FStar_Syntax_Print.term_to_string
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____1930 =
                                                FStar_Syntax_Print.term_to_string
                                                  c'.FStar_Syntax_Syntax.res_typ in
                                              FStar_Util.format3
                                                "Unexpected result type of computation. The computation type %s of the term %s should have type Type n for some level n but has type %s"
                                                uu____1928 uu____1929
                                                uu____1930 in
                                            failwith uu____1927);
                                       u))) in
                      let repr =
                        let uu____1932 = c.FStar_Syntax_Syntax.comp () in
                        FStar_TypeChecker_Env.reify_comp env1 uu____1932 u_c in
                      let e3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_app
                              (reify_op, [(e2, aqual)])))
                          (Some (repr.FStar_Syntax_Syntax.n))
                          top.FStar_Syntax_Syntax.pos in
                      let c1 =
                        let uu____1954 = FStar_Syntax_Syntax.mk_Total repr in
                        FStar_All.pipe_right uu____1954
                          FStar_Syntax_Util.lcomp_of_comp in
                      let uu____1955 = comp_check_expected_typ env1 e3 c1 in
                      (match uu____1955 with
                       | (e4,c2,g') ->
                           let uu____1965 =
                             FStar_TypeChecker_Rel.conj_guard g g' in
                           (e4, c2, uu____1965)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.tk = uu____1967;
              FStar_Syntax_Syntax.pos = uu____1968;
              FStar_Syntax_Syntax.vars = uu____1969;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.warn e1.FStar_Syntax_Syntax.pos
                "Qualifier on argument to reflect is irrelevant and will be ignored"
            else ();
            (let no_reflect uu____2001 =
               let uu____2002 =
                 let uu____2003 =
                   let uu____2006 =
                     FStar_Util.format1 "Effect %s cannot be reified"
                       l.FStar_Ident.str in
                   (uu____2006, (e1.FStar_Syntax_Syntax.pos)) in
                 FStar_Errors.Error uu____2003 in
               Prims.raise uu____2002 in
             let uu____2010 = FStar_Syntax_Util.head_and_args top in
             match uu____2010 with
             | (reflect_op,uu____2024) ->
                 let uu____2039 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l in
                 (match uu____2039 with
                  | None  -> no_reflect ()
                  | Some ed ->
                      let uu____2045 =
                        let uu____2046 =
                          FStar_All.pipe_right
                            ed.FStar_Syntax_Syntax.qualifiers
                            FStar_Syntax_Syntax.contains_reflectable in
                        Prims.op_Negation uu____2046 in
                      if uu____2045
                      then no_reflect ()
                      else
                        (let uu____2052 =
                           FStar_TypeChecker_Env.clear_expected_typ env1 in
                         match uu____2052 with
                         | (env_no_ex,topt) ->
                             let uu____2063 =
                               let u = FStar_TypeChecker_Env.new_u_univ () in
                               let repr =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u] env1 ed
                                   ([], (ed.FStar_Syntax_Syntax.repr)) in
                               let t =
                                 let uu____2078 =
                                   let uu____2081 =
                                     let uu____2082 =
                                       let uu____2092 =
                                         let uu____2094 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun in
                                         let uu____2095 =
                                           let uu____2097 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.tun in
                                           [uu____2097] in
                                         uu____2094 :: uu____2095 in
                                       (repr, uu____2092) in
                                     FStar_Syntax_Syntax.Tm_app uu____2082 in
                                   FStar_Syntax_Syntax.mk uu____2081 in
                                 uu____2078 None top.FStar_Syntax_Syntax.pos in
                               let uu____2107 =
                                 let uu____2111 =
                                   let uu____2112 =
                                     FStar_TypeChecker_Env.clear_expected_typ
                                       env1 in
                                   FStar_All.pipe_right uu____2112 Prims.fst in
                                 tc_tot_or_gtot_term uu____2111 t in
                               match uu____2107 with
                               | (t1,uu____2129,g) ->
                                   let uu____2131 =
                                     let uu____2132 =
                                       FStar_Syntax_Subst.compress t1 in
                                     uu____2132.FStar_Syntax_Syntax.n in
                                   (match uu____2131 with
                                    | FStar_Syntax_Syntax.Tm_app
                                        (uu____2143,(res,uu____2145)::
                                         (wp,uu____2147)::[])
                                        -> (t1, res, wp, g)
                                    | uu____2181 -> failwith "Impossible") in
                             (match uu____2063 with
                              | (expected_repr_typ,res_typ,wp,g0) ->
                                  let uu____2205 =
                                    let uu____2208 =
                                      tc_tot_or_gtot_term env_no_ex e1 in
                                    match uu____2208 with
                                    | (e2,c,g) ->
                                        ((let uu____2218 =
                                            let uu____2219 =
                                              FStar_Syntax_Util.is_total_lcomp
                                                c in
                                            FStar_All.pipe_left
                                              Prims.op_Negation uu____2219 in
                                          if uu____2218
                                          then
                                            FStar_TypeChecker_Err.add_errors
                                              env1
                                              [("Expected Tot, got a GTot computation",
                                                 (e2.FStar_Syntax_Syntax.pos))]
                                          else ());
                                         (let uu____2225 =
                                            FStar_TypeChecker_Rel.try_teq
                                              env_no_ex
                                              c.FStar_Syntax_Syntax.res_typ
                                              expected_repr_typ in
                                          match uu____2225 with
                                          | None  ->
                                              ((let uu____2230 =
                                                  let uu____2234 =
                                                    let uu____2237 =
                                                      let uu____2238 =
                                                        FStar_Syntax_Print.term_to_string
                                                          ed.FStar_Syntax_Syntax.repr in
                                                      let uu____2239 =
                                                        FStar_Syntax_Print.term_to_string
                                                          c.FStar_Syntax_Syntax.res_typ in
                                                      FStar_Util.format2
                                                        "Expected an instance of %s; got %s"
                                                        uu____2238 uu____2239 in
                                                    (uu____2237,
                                                      (e2.FStar_Syntax_Syntax.pos)) in
                                                  [uu____2234] in
                                                FStar_TypeChecker_Err.add_errors
                                                  env1 uu____2230);
                                               (let uu____2244 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                (e2, uu____2244)))
                                          | Some g' ->
                                              let uu____2246 =
                                                let uu____2247 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g0 in
                                                FStar_TypeChecker_Rel.conj_guard
                                                  g' uu____2247 in
                                              (e2, uu____2246))) in
                                  (match uu____2205 with
                                   | (e2,g) ->
                                       let c =
                                         let uu____2254 =
                                           let uu____2255 =
                                             let uu____2256 =
                                               let uu____2257 =
                                                 env1.FStar_TypeChecker_Env.universe_of
                                                   env1 res_typ in
                                               [uu____2257] in
                                             let uu____2258 =
                                               let uu____2264 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp in
                                               [uu____2264] in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____2256;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 (ed.FStar_Syntax_Syntax.mname);
                                               FStar_Syntax_Syntax.result_typ
                                                 = res_typ;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____2258;
                                               FStar_Syntax_Syntax.flags = []
                                             } in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____2255 in
                                         FStar_All.pipe_right uu____2254
                                           FStar_Syntax_Util.lcomp_of_comp in
                                       let e3 =
                                         (FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (reflect_op, [(e2, aqual)])))
                                           (Some
                                              (res_typ.FStar_Syntax_Syntax.n))
                                           top.FStar_Syntax_Syntax.pos in
                                       let uu____2285 =
                                         comp_check_expected_typ env1 e3 c in
                                       (match uu____2285 with
                                        | (e4,c1,g') ->
                                            let uu____2295 =
                                              FStar_TypeChecker_Rel.conj_guard
                                                g' g in
                                            (e4, c1, uu____2295))))))))
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1 in
           let env2 =
             let uu____2314 =
               let uu____2315 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               FStar_All.pipe_right uu____2315 Prims.fst in
             FStar_All.pipe_right uu____2314 instantiate_both in
           ((let uu____2324 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High in
             if uu____2324
             then
               let uu____2325 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
               let uu____2326 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print2 "(%s) Checking app %s\n" uu____2325
                 uu____2326
             else ());
            (let uu____2328 = tc_term (no_inst env2) head1 in
             match uu____2328 with
             | (head2,chead,g_head) ->
                 let uu____2338 =
                   let uu____2342 =
                     (Prims.op_Negation env2.FStar_TypeChecker_Env.lax) &&
                       (FStar_TypeChecker_Util.short_circuit_head head2) in
                   if uu____2342
                   then
                     let uu____2346 = FStar_TypeChecker_Env.expected_typ env0 in
                     check_short_circuit_args env2 head2 chead g_head args
                       uu____2346
                   else
                     (let uu____2349 =
                        FStar_TypeChecker_Env.expected_typ env0 in
                      check_application_args env2 head2 chead g_head args
                        uu____2349) in
                 (match uu____2338 with
                  | (e1,c,g) ->
                      ((let uu____2358 =
                          FStar_TypeChecker_Env.debug env2
                            FStar_Options.Extreme in
                        if uu____2358
                        then
                          let uu____2359 =
                            FStar_TypeChecker_Rel.print_pending_implicits g in
                          FStar_Util.print1
                            "Introduced {%s} implicits in application\n"
                            uu____2359
                        else ());
                       (let c1 =
                          let uu____2362 =
                            ((FStar_TypeChecker_Env.should_verify env2) &&
                               (let uu____2363 =
                                  FStar_Syntax_Util.is_lcomp_partial_return c in
                                Prims.op_Negation uu____2363))
                              && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c) in
                          if uu____2362
                          then
                            FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                              env2 e1 c
                          else c in
                        let uu____2365 = comp_check_expected_typ env0 e1 c1 in
                        match uu____2365 with
                        | (e2,c2,g') ->
                            let gimp =
                              let uu____2376 =
                                let uu____2377 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____2377.FStar_Syntax_Syntax.n in
                              match uu____2376 with
                              | FStar_Syntax_Syntax.Tm_uvar (u,uu____2381) ->
                                  let imp =
                                    ("head of application is a uvar", env0,
                                      u, e2,
                                      (c2.FStar_Syntax_Syntax.res_typ),
                                      (head2.FStar_Syntax_Syntax.pos)) in
                                  let uu___94_2413 =
                                    FStar_TypeChecker_Rel.trivial_guard in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___94_2413.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___94_2413.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___94_2413.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits = [imp]
                                  }
                              | uu____2438 ->
                                  FStar_TypeChecker_Rel.trivial_guard in
                            let gres =
                              let uu____2440 =
                                FStar_TypeChecker_Rel.conj_guard g' gimp in
                              FStar_TypeChecker_Rel.conj_guard g uu____2440 in
                            ((let uu____2442 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.Extreme in
                              if uu____2442
                              then
                                let uu____2443 =
                                  FStar_Syntax_Print.term_to_string e2 in
                                let uu____2444 =
                                  FStar_TypeChecker_Rel.guard_to_string env2
                                    gres in
                                FStar_Util.print2
                                  "Guard from application node %s is %s\n"
                                  uu____2443 uu____2444
                              else ());
                             (e2, c2, gres)))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____2474 = FStar_TypeChecker_Env.clear_expected_typ env1 in
           (match uu____2474 with
            | (env11,topt) ->
                let env12 = instantiate_both env11 in
                let uu____2486 = tc_term env12 e1 in
                (match uu____2486 with
                 | (e11,c1,g1) ->
                     let uu____2496 =
                       match topt with
                       | Some t -> (env1, t)
                       | None  ->
                           let uu____2502 = FStar_Syntax_Util.type_u () in
                           (match uu____2502 with
                            | (k,uu____2508) ->
                                let res_t =
                                  FStar_TypeChecker_Util.new_uvar env1 k in
                                let uu____2510 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    res_t in
                                (uu____2510, res_t)) in
                     (match uu____2496 with
                      | (env_branches,res_t) ->
                          ((let uu____2517 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme in
                            if uu____2517
                            then
                              let uu____2518 =
                                FStar_Syntax_Print.term_to_string res_t in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____2518
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (Some (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_Syntax_Syntax.res_typ in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches)) in
                            let uu____2569 =
                              let uu____2572 =
                                FStar_List.fold_right
                                  (fun uu____2591  ->
                                     fun uu____2592  ->
                                       match (uu____2591, uu____2592) with
                                       | ((uu____2624,f,c,g),(caccum,gaccum))
                                           ->
                                           let uu____2657 =
                                             FStar_TypeChecker_Rel.conj_guard
                                               g gaccum in
                                           (((f, c) :: caccum), uu____2657))
                                  t_eqns
                                  ([], FStar_TypeChecker_Rel.trivial_guard) in
                              match uu____2572 with
                              | (cases,g) ->
                                  let uu____2678 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases in
                                  (uu____2678, g) in
                            match uu____2569 with
                            | (c_branches,g_branches) ->
                                let cres =
                                  FStar_TypeChecker_Util.bind
                                    e11.FStar_Syntax_Syntax.pos env1
                                    (Some e11) c1
                                    ((Some guard_x), c_branches) in
                                let e2 =
                                  let mk_match scrutinee =
                                    let branches =
                                      FStar_All.pipe_right t_eqns
                                        (FStar_List.map
                                           (fun uu____2731  ->
                                              match uu____2731 with
                                              | ((pat,wopt,br),uu____2747,lc,uu____2749)
                                                  ->
                                                  let uu____2756 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br
                                                      lc.FStar_Syntax_Syntax.eff_name
                                                      cres.FStar_Syntax_Syntax.eff_name
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  (pat, wopt, uu____2756))) in
                                    let e2 =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_match
                                            (scrutinee, branches)))
                                        (Some
                                           ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos in
                                    let e3 =
                                      FStar_TypeChecker_Util.maybe_monadic
                                        env1 e2
                                        cres.FStar_Syntax_Syntax.eff_name
                                        cres.FStar_Syntax_Syntax.res_typ in
                                    (FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_ascribed
                                          (e3,
                                            (FStar_Util.Inl
                                               (cres.FStar_Syntax_Syntax.res_typ)),
                                            (Some
                                               (cres.FStar_Syntax_Syntax.eff_name)))))
                                      None e3.FStar_Syntax_Syntax.pos in
                                  let uu____2796 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1 c1.FStar_Syntax_Syntax.eff_name in
                                  if uu____2796
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____2803 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x in
                                       mk_match uu____2803 in
                                     let lb =
                                       let uu____2807 =
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
                                           uu____2807;
                                         FStar_Syntax_Syntax.lbdef = e11
                                       } in
                                     let e2 =
                                       let uu____2811 =
                                         let uu____2814 =
                                           let uu____2815 =
                                             let uu____2823 =
                                               let uu____2824 =
                                                 let uu____2825 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x in
                                                 [uu____2825] in
                                               FStar_Syntax_Subst.close
                                                 uu____2824 e_match in
                                             ((false, [lb]), uu____2823) in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____2815 in
                                         FStar_Syntax_Syntax.mk uu____2814 in
                                       uu____2811
                                         (Some
                                            ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         top.FStar_Syntax_Syntax.pos in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_Syntax_Syntax.eff_name
                                       cres.FStar_Syntax_Syntax.res_typ) in
                                ((let uu____2839 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme in
                                  if uu____2839
                                  then
                                    let uu____2840 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____2841 =
                                      let uu____2842 =
                                        cres.FStar_Syntax_Syntax.comp () in
                                      FStar_All.pipe_left
                                        FStar_Syntax_Print.comp_to_string
                                        uu____2842 in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____2840 uu____2841
                                  else ());
                                 (let uu____2844 =
                                    FStar_TypeChecker_Rel.conj_guard g1
                                      g_branches in
                                  (e2, cres, uu____2844))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2847;
                FStar_Syntax_Syntax.lbunivs = uu____2848;
                FStar_Syntax_Syntax.lbtyp = uu____2849;
                FStar_Syntax_Syntax.lbeff = uu____2850;
                FStar_Syntax_Syntax.lbdef = uu____2851;_}::[]),uu____2852)
           ->
           ((let uu____2867 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____2867
             then
               let uu____2868 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____2868
             else ());
            check_top_level_let env1 top)
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____2870),uu____2871) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____2881;
                FStar_Syntax_Syntax.lbunivs = uu____2882;
                FStar_Syntax_Syntax.lbtyp = uu____2883;
                FStar_Syntax_Syntax.lbeff = uu____2884;
                FStar_Syntax_Syntax.lbdef = uu____2885;_}::uu____2886),uu____2887)
           ->
           ((let uu____2903 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
             if uu____2903
             then
               let uu____2904 = FStar_Syntax_Print.term_to_string top in
               FStar_Util.print1 "%s\n" uu____2904
             else ());
            check_top_level_let_rec env1 top)
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____2906),uu____2907) ->
           check_inner_let_rec env1 top)
and tc_value:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t =
        let uu____2951 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
        match uu____2951 with
        | (e2,t1,implicits) ->
            let tc =
              let uu____2964 = FStar_TypeChecker_Env.should_verify env1 in
              if uu____2964
              then FStar_Util.Inl t1
              else
                (let uu____2968 =
                   let uu____2969 = FStar_Syntax_Syntax.mk_Total t1 in
                   FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                     uu____2969 in
                 FStar_Util.Inr uu____2968) in
            let is_data_ctor uu___82_2978 =
              match uu___82_2978 with
              | Some (FStar_Syntax_Syntax.Data_ctor )|Some
                (FStar_Syntax_Syntax.Record_ctor _) -> true
              | uu____2981 -> false in
            let uu____2983 =
              (is_data_ctor dc) &&
                (let uu____2984 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v in
                 Prims.op_Negation uu____2984) in
            if uu____2983
            then
              let uu____2990 =
                let uu____2991 =
                  let uu____2994 =
                    FStar_Util.format1 "Expected a data constructor; got %s"
                      (v1.FStar_Syntax_Syntax.v).FStar_Ident.str in
                  let uu____2997 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____2994, uu____2997) in
                FStar_Errors.Error uu____2991 in
              Prims.raise uu____2990
            else value_check_expected_typ env1 e2 tc implicits in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos in
      let top = FStar_Syntax_Subst.compress e in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____3008 =
            let uu____3009 = FStar_Syntax_Print.term_to_string top in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____3009 in
          failwith uu____3008
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let g =
            let uu____3028 =
              let uu____3029 = FStar_Syntax_Subst.compress t1 in
              uu____3029.FStar_Syntax_Syntax.n in
            match uu____3028 with
            | FStar_Syntax_Syntax.Tm_arrow uu____3032 ->
                FStar_TypeChecker_Rel.trivial_guard
            | uu____3040 ->
                let imp =
                  ("uvar in term", env1, u, top, t1,
                    (top.FStar_Syntax_Syntax.pos)) in
                let uu___95_3060 = FStar_TypeChecker_Rel.trivial_guard in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___95_3060.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred =
                    (uu___95_3060.FStar_TypeChecker_Env.deferred);
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___95_3060.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits = [imp]
                } in
          value_check_expected_typ env1 e (FStar_Util.Inl t1) g
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1 in
          let uu____3088 =
            let uu____3095 = FStar_TypeChecker_Env.expected_typ env1 in
            match uu____3095 with
            | None  ->
                let uu____3103 = FStar_Syntax_Util.type_u () in
                (match uu____3103 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | Some t -> (t, [], FStar_TypeChecker_Rel.trivial_guard) in
          (match uu____3088 with
           | (t,uu____3124,g0) ->
               let uu____3132 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t in
               (match uu____3132 with
                | (e1,uu____3143,g1) ->
                    let uu____3151 =
                      let uu____3152 = FStar_Syntax_Syntax.mk_Total t in
                      FStar_All.pipe_right uu____3152
                        FStar_Syntax_Util.lcomp_of_comp in
                    let uu____3153 = FStar_TypeChecker_Rel.conj_guard g0 g1 in
                    (e1, uu____3151, uu____3153)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____3155 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____3164 = FStar_Syntax_Syntax.range_of_bv x in
              ((x.FStar_Syntax_Syntax.sort), uu____3164)
            else FStar_TypeChecker_Env.lookup_bv env1 x in
          (match uu____3155 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___96_3178 = x in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___96_3178.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___96_3178.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng in
               (FStar_TypeChecker_Common.insert_bv x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1 in
                 let uu____3181 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t in
                 match uu____3181 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____3194 =
                         FStar_TypeChecker_Env.should_verify env1 in
                       if uu____3194
                       then FStar_Util.Inl t1
                       else
                         (let uu____3198 =
                            let uu____3199 = FStar_Syntax_Syntax.mk_Total t1 in
                            FStar_All.pipe_left
                              FStar_Syntax_Util.lcomp_of_comp uu____3199 in
                          FStar_Util.Inr uu____3198) in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3205;
             FStar_Syntax_Syntax.pos = uu____3206;
             FStar_Syntax_Syntax.vars = uu____3207;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us in
          let uu____3215 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3215 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____3237 =
                     let uu____3238 =
                       let uu____3241 = FStar_TypeChecker_Env.get_range env1 in
                       ("Unexpected number of universe instantiations",
                         uu____3241) in
                     FStar_Errors.Error uu____3238 in
                   Prims.raise uu____3237)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____3249 -> failwith "Impossible") us' us1;
                (let fv' =
                   let uu___97_3251 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___98_3252 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___98_3252.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___98_3252.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___97_3251.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___97_3251.FStar_Syntax_Syntax.fv_qual)
                   } in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
                    let uu____3268 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3268 us1 in
                  check_instantiated_fvar env1
                    fv'1.FStar_Syntax_Syntax.fv_name
                    fv'1.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3280 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3280 with
           | ((us,t),range) ->
               ((let uu____3298 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range") in
                 if uu____3298
                 then
                   let uu____3299 =
                     let uu____3300 = FStar_Syntax_Syntax.lid_of_fv fv in
                     FStar_Syntax_Print.lid_to_string uu____3300 in
                   let uu____3301 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos in
                   let uu____3302 = FStar_Range.string_of_range range in
                   let uu____3303 = FStar_Range.string_of_use_range range in
                   let uu____3304 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got type %s"
                     uu____3299 uu____3301 uu____3302 uu____3303 uu____3304
                 else ());
                (let fv' =
                   let uu___99_3307 = fv in
                   {
                     FStar_Syntax_Syntax.fv_name =
                       (let uu___100_3308 = fv.FStar_Syntax_Syntax.fv_name in
                        {
                          FStar_Syntax_Syntax.v =
                            (uu___100_3308.FStar_Syntax_Syntax.v);
                          FStar_Syntax_Syntax.ty = t;
                          FStar_Syntax_Syntax.p =
                            (uu___100_3308.FStar_Syntax_Syntax.p)
                        });
                     FStar_Syntax_Syntax.fv_delta =
                       (uu___99_3307.FStar_Syntax_Syntax.fv_delta);
                     FStar_Syntax_Syntax.fv_qual =
                       (uu___99_3307.FStar_Syntax_Syntax.fv_qual)
                   } in
                 let fv'1 = FStar_Syntax_Syntax.set_range_of_fv fv' range in
                 FStar_TypeChecker_Common.insert_fv fv'1 t;
                 (let e1 =
                    let uu____3324 =
                      (FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_fvar fv'1))
                        (Some (t.FStar_Syntax_Syntax.n))
                        e.FStar_Syntax_Syntax.pos in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3324 us in
                  check_instantiated_fvar env1
                    fv'1.FStar_Syntax_Syntax.fv_name
                    fv'1.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant top.FStar_Syntax_Syntax.pos c in
          let e1 =
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c))
              (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____3360 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3360 with
           | (bs1,c1) ->
               let env0 = env1 in
               let uu____3369 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3369 with
                | (env2,uu____3377) ->
                    let uu____3380 = tc_binders env2 bs1 in
                    (match uu____3380 with
                     | (bs2,env3,g,us) ->
                         let uu____3392 = tc_comp env3 c1 in
                         (match uu____3392 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___101_3405 =
                                  FStar_Syntax_Util.arrow bs2 c2 in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___101_3405.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___101_3405.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___101_3405.FStar_Syntax_Syntax.vars)
                                } in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us) in
                                let t =
                                  (FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u)) None
                                    top.FStar_Syntax_Syntax.pos in
                                let g1 =
                                  let uu____3426 =
                                    FStar_TypeChecker_Rel.close_guard bs2 f in
                                  FStar_TypeChecker_Rel.conj_guard g
                                    uu____3426 in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_type u ->
          let u1 = tc_universe env1 u in
          let t =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u1)))
              None top.FStar_Syntax_Syntax.pos in
          let e1 =
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1))
              (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Rel.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____3461 =
            let uu____3464 =
              let uu____3465 = FStar_Syntax_Syntax.mk_binder x in
              [uu____3465] in
            FStar_Syntax_Subst.open_term uu____3464 phi in
          (match uu____3461 with
           | (x1,phi1) ->
               let env0 = env1 in
               let uu____3472 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____3472 with
                | (env2,uu____3480) ->
                    let uu____3483 =
                      let uu____3490 = FStar_List.hd x1 in
                      tc_binder env2 uu____3490 in
                    (match uu____3483 with
                     | (x2,env3,f1,u) ->
                         ((let uu____3507 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High in
                           if uu____3507
                           then
                             let uu____3508 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos in
                             let uu____3509 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____3510 =
                               FStar_Syntax_Print.bv_to_string (Prims.fst x2) in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____3508 uu____3509 uu____3510
                           else ());
                          (let uu____3512 = FStar_Syntax_Util.type_u () in
                           match uu____3512 with
                           | (t_phi,uu____3519) ->
                               let uu____3520 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi in
                               (match uu____3520 with
                                | (phi2,uu____3528,f2) ->
                                    let e1 =
                                      let uu___102_3533 =
                                        FStar_Syntax_Util.refine
                                          (Prims.fst x2) phi2 in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___102_3533.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.tk =
                                          (uu___102_3533.FStar_Syntax_Syntax.tk);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___102_3533.FStar_Syntax_Syntax.vars)
                                      } in
                                    let t =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_type u))
                                        None top.FStar_Syntax_Syntax.pos in
                                    let g =
                                      let uu____3552 =
                                        FStar_TypeChecker_Rel.close_guard
                                          [x2] f2 in
                                      FStar_TypeChecker_Rel.conj_guard f1
                                        uu____3552 in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____3561) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs in
          ((let uu____3586 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
            if uu____3586
            then
              let uu____3587 =
                FStar_Syntax_Print.term_to_string
                  (let uu___103_3588 = top in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs (bs1, body, None));
                     FStar_Syntax_Syntax.tk =
                       (uu___103_3588.FStar_Syntax_Syntax.tk);
                     FStar_Syntax_Syntax.pos =
                       (uu___103_3588.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___103_3588.FStar_Syntax_Syntax.vars)
                   }) in
              FStar_Util.print1 "Abstraction is: %s\n" uu____3587
            else ());
           (let uu____3607 = FStar_Syntax_Subst.open_term bs1 body in
            match uu____3607 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____3615 ->
          let uu____3616 =
            let uu____3617 = FStar_Syntax_Print.term_to_string top in
            let uu____3618 = FStar_Syntax_Print.tag_of_term top in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____3617
              uu____3618 in
          failwith uu____3616
and tc_constant:
  FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun r  ->
    fun c  ->
      match c with
      | FStar_Const.Const_unit  -> FStar_TypeChecker_Common.t_unit
      | FStar_Const.Const_bool uu____3624 -> FStar_TypeChecker_Common.t_bool
      | FStar_Const.Const_int (uu____3625,None ) ->
          FStar_TypeChecker_Common.t_int
      | FStar_Const.Const_int (uu____3631,Some uu____3632) ->
          failwith "machine integers should be desugared"
      | FStar_Const.Const_string uu____3640 ->
          FStar_TypeChecker_Common.t_string
      | FStar_Const.Const_float uu____3644 ->
          FStar_TypeChecker_Common.t_float
      | FStar_Const.Const_char uu____3645 -> FStar_TypeChecker_Common.t_char
      | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
      | FStar_Const.Const_range uu____3646 ->
          FStar_TypeChecker_Common.t_range
      | uu____3647 ->
          Prims.raise (FStar_Errors.Error ("Unsupported constant", r))
and tc_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp* FStar_Syntax_Syntax.universe*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun c  ->
      let c0 = c in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uu____3658) ->
          let uu____3665 = FStar_Syntax_Util.type_u () in
          (match uu____3665 with
           | (k,u) ->
               let uu____3673 = tc_check_tot_or_gtot_term env t k in
               (match uu____3673 with
                | (t1,uu____3681,g) ->
                    let uu____3683 =
                      FStar_Syntax_Syntax.mk_Total' t1 (Some u) in
                    (uu____3683, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____3685) ->
          let uu____3692 = FStar_Syntax_Util.type_u () in
          (match uu____3692 with
           | (k,u) ->
               let uu____3700 = tc_check_tot_or_gtot_term env t k in
               (match uu____3700 with
                | (t1,uu____3708,g) ->
                    let uu____3710 =
                      FStar_Syntax_Syntax.mk_GTotal' t1 (Some u) in
                    (uu____3710, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head1 =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.Delta_constant None in
          let head2 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head1
            | us ->
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_uinst (head1, us))) None
                  c0.FStar_Syntax_Syntax.pos in
          let tc =
            let uu____3726 =
              let uu____3727 =
                let uu____3728 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ in
                uu____3728 :: (c1.FStar_Syntax_Syntax.effect_args) in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____3727 in
            uu____3726 None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
          let uu____3733 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff in
          (match uu____3733 with
           | (tc1,uu____3741,f) ->
               let uu____3743 = FStar_Syntax_Util.head_and_args tc1 in
               (match uu____3743 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____3773 =
                        let uu____3774 = FStar_Syntax_Subst.compress head3 in
                        uu____3774.FStar_Syntax_Syntax.n in
                      match uu____3773 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____3777,us) -> us
                      | uu____3783 -> [] in
                    let uu____3784 = FStar_Syntax_Util.head_and_args tc1 in
                    (match uu____3784 with
                     | (uu____3797,args1) ->
                         let uu____3813 =
                           let uu____3825 = FStar_List.hd args1 in
                           let uu____3834 = FStar_List.tl args1 in
                           (uu____3825, uu____3834) in
                         (match uu____3813 with
                          | (res,args2) ->
                              let uu____3876 =
                                let uu____3881 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___83_3891  ->
                                          match uu___83_3891 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____3897 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env in
                                              (match uu____3897 with
                                               | (env1,uu____3904) ->
                                                   let uu____3907 =
                                                     tc_tot_or_gtot_term env1
                                                       e in
                                                   (match uu____3907 with
                                                    | (e1,uu____3914,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Rel.trivial_guard))) in
                                FStar_All.pipe_right uu____3881
                                  FStar_List.unzip in
                              (match uu____3876 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (Prims.fst res) in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___104_3937 = c1 in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___104_3937.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (Prims.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___104_3937.FStar_Syntax_Syntax.flags)
                                        }) in
                                   let u_c =
                                     let uu____3941 =
                                       FStar_TypeChecker_Env.effect_repr env
                                         c2 u in
                                     match uu____3941 with
                                     | None  -> u
                                     | Some tm ->
                                         env.FStar_TypeChecker_Env.universe_of
                                           env tm in
                                   let uu____3944 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Rel.conj_guard f
                                       guards in
                                   (c2, u_c, uu____3944))))))
and tc_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____3952 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif _|FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3955 = aux u3 in FStar_Syntax_Syntax.U_succ uu____3955
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3958 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____3958
        | FStar_Syntax_Syntax.U_name x -> u2 in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____3962 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____3962 Prims.snd
         | uu____3967 -> aux u)
and tc_abs:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
            FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun top  ->
      fun bs  ->
        fun body  ->
          let fail msg t =
            let uu____3988 =
              let uu____3989 =
                let uu____3992 =
                  FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                    env msg t top in
                (uu____3992, (top.FStar_Syntax_Syntax.pos)) in
              FStar_Errors.Error uu____3989 in
            Prims.raise uu____3988 in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____4046 bs2 bs_expected1 =
              match uu____4046 with
              | (env2,out,g,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) -> (env2, (FStar_List.rev out), None, g, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((match (imp, imp') with
                         | (None ,Some (FStar_Syntax_Syntax.Implicit _))
                           |(Some (FStar_Syntax_Syntax.Implicit _),None ) ->
                             let uu____4143 =
                               let uu____4144 =
                                 let uu____4147 =
                                   let uu____4148 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.format1
                                     "Inconsistent implicit argument annotation on argument %s"
                                     uu____4148 in
                                 let uu____4149 =
                                   FStar_Syntax_Syntax.range_of_bv hd1 in
                                 (uu____4147, uu____4149) in
                               FStar_Errors.Error uu____4144 in
                             Prims.raise uu____4143
                         | uu____4150 -> ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort in
                         let uu____4154 =
                           let uu____4157 =
                             let uu____4158 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort in
                             uu____4158.FStar_Syntax_Syntax.n in
                           match uu____4157 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t, g)
                           | uu____4163 ->
                               ((let uu____4165 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High in
                                 if uu____4165
                                 then
                                   let uu____4166 =
                                     FStar_Syntax_Print.bv_to_string hd1 in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____4166
                                 else ());
                                (let uu____4168 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort in
                                 match uu____4168 with
                                 | (t,uu____4175,g1) ->
                                     let g2 =
                                       let uu____4178 =
                                         FStar_TypeChecker_Env.get_range env2 in
                                       let uu____4179 =
                                         FStar_TypeChecker_Rel.teq env2 t
                                           expected_t in
                                       FStar_TypeChecker_Util.label_guard
                                         uu____4178
                                         "Type annotation on parameter incompatible with the expected type"
                                         uu____4179 in
                                     let g3 =
                                       let uu____4181 =
                                         FStar_TypeChecker_Rel.conj_guard g1
                                           g2 in
                                       FStar_TypeChecker_Rel.conj_guard g
                                         uu____4181 in
                                     (t, g3))) in
                         match uu____4154 with
                         | (t,g1) ->
                             let hd2 =
                               let uu___105_4197 = hd1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___105_4197.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___105_4197.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               } in
                             let b = (hd2, imp) in
                             let b_expected = (hd_expected, imp') in
                             let env3 = push_binding env2 b in
                             let subst2 =
                               let uu____4206 =
                                 FStar_Syntax_Syntax.bv_to_name hd2 in
                               maybe_extend_subst subst1 b_expected
                                 uu____4206 in
                             aux (env3, (b :: out), g1, subst2) bs3
                               bs_expected2))
                   | (rest,[]) ->
                       (env2, (FStar_List.rev out),
                         (Some (FStar_Util.Inl rest)), g, subst1)
                   | ([],rest) ->
                       (env2, (FStar_List.rev out),
                         (Some (FStar_Util.Inr rest)), g, subst1)) in
            aux (env1, [], FStar_TypeChecker_Rel.trivial_guard, []) bs1
              bs_expected in
          let rec expected_function_typ1 env1 t0 body1 =
            match t0 with
            | None  ->
                ((match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____4302 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____4306 = tc_binders env1 bs in
                  match uu____4306 with
                  | (bs1,envbody,g,uu____4325) ->
                      let uu____4326 =
                        let uu____4331 =
                          let uu____4332 = FStar_Syntax_Subst.compress body1 in
                          uu____4332.FStar_Syntax_Syntax.n in
                        match uu____4331 with
                        | FStar_Syntax_Syntax.Tm_ascribed
                            (e,FStar_Util.Inr c,uu____4341) ->
                            let uu____4360 = tc_comp envbody c in
                            (match uu____4360 with
                             | (c1,uu____4369,g') ->
                                 let uu____4371 =
                                   FStar_TypeChecker_Rel.conj_guard g g' in
                                 ((Some c1), body1, uu____4371))
                        | uu____4373 -> (None, body1, g) in
                      (match uu____4326 with
                       | (copt,body2,g1) ->
                           (None, bs1, [], copt, envbody, body2, g1))))
            | Some t ->
                let t1 = FStar_Syntax_Subst.compress t in
                let rec as_function_typ norm1 t2 =
                  let uu____4423 =
                    let uu____4424 = FStar_Syntax_Subst.compress t2 in
                    uu____4424.FStar_Syntax_Syntax.n in
                  match uu____4423 with
                  | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
                    ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____4455 -> failwith "Impossible");
                       (let uu____4459 = tc_binders env1 bs in
                        match uu____4459 with
                        | (bs1,envbody,g,uu____4479) ->
                            let uu____4480 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody in
                            (match uu____4480 with
                             | (envbody1,uu____4497) ->
                                 ((Some (t2, true)), bs1, [], None, envbody1,
                                   body1, g))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____4508) ->
                      let uu____4513 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort in
                      (match uu____4513 with
                       | (uu____4538,bs1,bs',copt,env2,body2,g) ->
                           ((Some (t2, false)), bs1, bs', copt, env2, body2,
                             g))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____4574 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected in
                      (match uu____4574 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 =
                             let rec handle_more uu____4635 c_expected2 =
                               match uu____4635 with
                               | (env3,bs2,more,guard,subst1) ->
                                   (match more with
                                    | None  ->
                                        let uu____4696 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        (env3, bs2, guard, uu____4696)
                                    | Some (FStar_Util.Inr more_bs_expected)
                                        ->
                                        let c =
                                          let uu____4713 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2 in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____4713 in
                                        let uu____4714 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c in
                                        (env3, bs2, guard, uu____4714)
                                    | Some (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2 in
                                        if FStar_Syntax_Util.is_named_tot c
                                        then
                                          let t3 =
                                            unfold_whnf env3
                                              (FStar_Syntax_Util.comp_result
                                                 c) in
                                          (match t3.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs_expected3,c_expected3) ->
                                               let uu____4755 =
                                                 check_binders env3 more_bs
                                                   bs_expected3 in
                                               (match uu____4755 with
                                                | (env4,bs',more1,guard',subst2)
                                                    ->
                                                    let uu____4782 =
                                                      let uu____4798 =
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          guard guard' in
                                                      (env4,
                                                        (FStar_List.append
                                                           bs2 bs'), more1,
                                                        uu____4798, subst2) in
                                                    handle_more uu____4782
                                                      c_expected3)
                                           | uu____4807 ->
                                               let uu____4808 =
                                                 let uu____4809 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t3 in
                                                 FStar_Util.format1
                                                   "More arguments than annotated type (%s)"
                                                   uu____4809 in
                                               fail uu____4808 t3)
                                        else
                                          fail
                                            "Function definition takes more arguments than expected from its annotated type"
                                            t2) in
                             let uu____4825 =
                               check_binders env2 bs1 bs_expected2 in
                             handle_more uu____4825 c_expected1 in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c in
                             let envbody1 =
                               let uu___106_4863 = envbody in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___106_4863.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___106_4863.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___106_4863.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___106_4863.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___106_4863.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___106_4863.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___106_4863.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___106_4863.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___106_4863.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___106_4863.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___106_4863.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___106_4863.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___106_4863.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___106_4863.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___106_4863.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___106_4863.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___106_4863.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___106_4863.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___106_4863.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___106_4863.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___106_4863.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___106_4863.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___106_4863.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             FStar_All.pipe_right letrecs
                               (FStar_List.fold_left
                                  (fun uu____4877  ->
                                     fun uu____4878  ->
                                       match (uu____4877, uu____4878) with
                                       | ((env2,letrec_binders),(l,t3)) ->
                                           let uu____4903 =
                                             let uu____4907 =
                                               let uu____4908 =
                                                 FStar_TypeChecker_Env.clear_expected_typ
                                                   env2 in
                                               FStar_All.pipe_right
                                                 uu____4908 Prims.fst in
                                             tc_term uu____4907 t3 in
                                           (match uu____4903 with
                                            | (t4,uu____4920,uu____4921) ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.push_let_binding
                                                    env2 l ([], t4) in
                                                let lb =
                                                  match l with
                                                  | FStar_Util.Inl x ->
                                                      let uu____4928 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          (let uu___107_4929
                                                             = x in
                                                           {
                                                             FStar_Syntax_Syntax.ppname
                                                               =
                                                               (uu___107_4929.FStar_Syntax_Syntax.ppname);
                                                             FStar_Syntax_Syntax.index
                                                               =
                                                               (uu___107_4929.FStar_Syntax_Syntax.index);
                                                             FStar_Syntax_Syntax.sort
                                                               = t4
                                                           }) in
                                                      uu____4928 ::
                                                        letrec_binders
                                                  | uu____4930 ->
                                                      letrec_binders in
                                                (env3, lb))) (envbody1, [])) in
                           let uu____4933 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 in
                           (match uu____4933 with
                            | (envbody,bs1,g,c) ->
                                let uu____4963 =
                                  let uu____4967 =
                                    FStar_TypeChecker_Env.should_verify env1 in
                                  if uu____4967
                                  then mk_letrec_env envbody bs1 c
                                  else (envbody, []) in
                                (match uu____4963 with
                                 | (envbody1,letrecs) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c) in
                                     ((Some (t2, false)), bs1, letrecs,
                                       (Some c), envbody2, body1, g))))
                  | uu____5000 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____5013 = unfold_whnf env1 t2 in
                        as_function_typ true uu____5013
                      else
                        (let uu____5015 =
                           expected_function_typ1 env1 None body1 in
                         match uu____5015 with
                         | (uu____5039,bs1,uu____5041,c_opt,envbody,body2,g)
                             ->
                             ((Some (t2, false)), bs1, [], c_opt, envbody,
                               body2, g)) in
                as_function_typ false t1 in
          let use_eq = env.FStar_TypeChecker_Env.use_eq in
          let uu____5062 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____5062 with
          | (env1,topt) ->
              ((let uu____5074 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High in
                if uu____5074
                then
                  let uu____5075 =
                    match topt with
                    | None  -> "None"
                    | Some t -> FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____5075
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____5079 = expected_function_typ1 env1 topt body in
                match uu____5079 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g) ->
                    let uu____5109 =
                      tc_term
                        (let uu___108_5113 = envbody in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___108_5113.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___108_5113.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___108_5113.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___108_5113.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___108_5113.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___108_5113.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___108_5113.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___108_5113.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___108_5113.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___108_5113.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___108_5113.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___108_5113.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___108_5113.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level = false;
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___108_5113.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq = use_eq;
                           FStar_TypeChecker_Env.is_iface =
                             (uu___108_5113.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___108_5113.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___108_5113.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___108_5113.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___108_5113.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___108_5113.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___108_5113.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___108_5113.FStar_TypeChecker_Env.qname_and_index)
                         }) body1 in
                    (match uu____5109 with
                     | (body2,cbody,guard_body) ->
                         let guard_body1 =
                           FStar_TypeChecker_Rel.solve_deferred_constraints
                             envbody guard_body in
                         ((let uu____5122 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Implicits") in
                           if uu____5122
                           then
                             let uu____5123 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length
                                    guard_body1.FStar_TypeChecker_Env.implicits) in
                             let uu____5132 =
                               let uu____5133 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               FStar_All.pipe_left
                                 FStar_Syntax_Print.comp_to_string uu____5133 in
                             FStar_Util.print2
                               "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n"
                               uu____5123 uu____5132
                           else ());
                          (let uu____5135 =
                             let uu____5139 =
                               let uu____5142 =
                                 cbody.FStar_Syntax_Syntax.comp () in
                               (body2, uu____5142) in
                             check_expected_effect
                               (let uu___109_5147 = envbody in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___109_5147.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___109_5147.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___109_5147.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___109_5147.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___109_5147.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___109_5147.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___109_5147.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___109_5147.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___109_5147.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___109_5147.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___109_5147.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___109_5147.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___109_5147.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___109_5147.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___109_5147.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq = use_eq;
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___109_5147.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___109_5147.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___109_5147.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___109_5147.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___109_5147.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___109_5147.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___109_5147.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___109_5147.FStar_TypeChecker_Env.qname_and_index)
                                }) c_opt uu____5139 in
                           match uu____5135 with
                           | (body3,cbody1,guard) ->
                               let guard1 =
                                 FStar_TypeChecker_Rel.conj_guard guard_body1
                                   guard in
                               let guard2 =
                                 let uu____5156 =
                                   env1.FStar_TypeChecker_Env.top_level ||
                                     (let uu____5157 =
                                        FStar_TypeChecker_Env.should_verify
                                          env1 in
                                      Prims.op_Negation uu____5157) in
                                 if uu____5156
                                 then
                                   let uu____5158 =
                                     FStar_TypeChecker_Rel.conj_guard g
                                       guard1 in
                                   FStar_TypeChecker_Rel.discharge_guard
                                     envbody uu____5158
                                 else
                                   (let guard2 =
                                      let uu____5161 =
                                        FStar_TypeChecker_Rel.conj_guard g
                                          guard1 in
                                      FStar_TypeChecker_Rel.close_guard
                                        (FStar_List.append bs1 letrec_binders)
                                        uu____5161 in
                                    guard2) in
                               let tfun_computed =
                                 FStar_Syntax_Util.arrow bs1 cbody1 in
                               let e =
                                 let uu____5168 =
                                   let uu____5175 =
                                     let uu____5181 =
                                       FStar_All.pipe_right
                                         (FStar_Util.dflt cbody1 c_opt)
                                         FStar_Syntax_Util.lcomp_of_comp in
                                     FStar_All.pipe_right uu____5181
                                       (fun _0_29  -> FStar_Util.Inl _0_29) in
                                   Some uu____5175 in
                                 FStar_Syntax_Util.abs bs1 body3 uu____5168 in
                               let uu____5195 =
                                 match tfun_opt with
                                 | Some (t,use_teq) ->
                                     let t1 = FStar_Syntax_Subst.compress t in
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          uu____5210 -> (e, t1, guard2)
                                      | uu____5218 ->
                                          let uu____5219 =
                                            if use_teq
                                            then
                                              let uu____5224 =
                                                FStar_TypeChecker_Rel.teq
                                                  env1 t1 tfun_computed in
                                              (e, uu____5224)
                                            else
                                              FStar_TypeChecker_Util.check_and_ascribe
                                                env1 e tfun_computed t1 in
                                          (match uu____5219 with
                                           | (e1,guard') ->
                                               let uu____5231 =
                                                 FStar_TypeChecker_Rel.conj_guard
                                                   guard2 guard' in
                                               (e1, t1, uu____5231)))
                                 | None  -> (e, tfun_computed, guard2) in
                               (match uu____5195 with
                                | (e1,tfun,guard3) ->
                                    let c =
                                      if env1.FStar_TypeChecker_Env.top_level
                                      then FStar_Syntax_Syntax.mk_Total tfun
                                      else
                                        FStar_TypeChecker_Util.return_value
                                          env1 tfun e1 in
                                    let uu____5244 =
                                      FStar_TypeChecker_Util.strengthen_precondition
                                        None env1 e1
                                        (FStar_Syntax_Util.lcomp_of_comp c)
                                        guard3 in
                                    (match uu____5244 with
                                     | (c1,g1) -> (e1, c1, g1))))))))
and check_application_args:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) Prims.list
            ->
            FStar_Syntax_Syntax.typ Prims.option ->
              ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.lcomp*
                FStar_TypeChecker_Env.guard_t)
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
              (let uu____5280 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High in
               if uu____5280
               then
                 let uu____5281 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos in
                 let uu____5282 = FStar_Syntax_Print.term_to_string thead in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____5281
                   uu____5282
               else ());
              (let monadic_application uu____5324 subst1 arg_comps_rev
                 arg_rets guard fvs bs =
                 match uu____5324 with
                 | (head2,chead1,ghead1,cres) ->
                     let rt =
                       check_no_escape (Some head2) env fvs
                         cres.FStar_Syntax_Syntax.res_typ in
                     let cres1 =
                       let uu___110_5365 = cres in
                       {
                         FStar_Syntax_Syntax.eff_name =
                           (uu___110_5365.FStar_Syntax_Syntax.eff_name);
                         FStar_Syntax_Syntax.res_typ = rt;
                         FStar_Syntax_Syntax.cflags =
                           (uu___110_5365.FStar_Syntax_Syntax.cflags);
                         FStar_Syntax_Syntax.comp =
                           (uu___110_5365.FStar_Syntax_Syntax.comp)
                       } in
                     let uu____5366 =
                       match bs with
                       | [] ->
                           let cres2 =
                             FStar_TypeChecker_Util.subst_lcomp subst1 cres1 in
                           let g =
                             FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                           let refine_with_equality =
                             (FStar_Syntax_Util.is_pure_or_ghost_lcomp cres2)
                               &&
                               (FStar_All.pipe_right arg_comps_rev
                                  (FStar_Util.for_some
                                     (fun uu___84_5393  ->
                                        match uu___84_5393 with
                                        | (uu____5402,uu____5403,FStar_Util.Inl
                                           uu____5404) -> false
                                        | (uu____5415,uu____5416,FStar_Util.Inr
                                           c) ->
                                            let uu____5426 =
                                              FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                c in
                                            Prims.op_Negation uu____5426))) in
                           let cres3 =
                             if refine_with_equality
                             then
                               let uu____5428 =
                                 (FStar_Syntax_Syntax.mk_Tm_app head2
                                    (FStar_List.rev arg_rets))
                                   (Some
                                      ((cres2.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                   r in
                               FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                 env uu____5428 cres2
                             else
                               ((let uu____5439 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low in
                                 if uu____5439
                                 then
                                   let uu____5440 =
                                     FStar_Syntax_Print.term_to_string head2 in
                                   let uu____5441 =
                                     FStar_Syntax_Print.lcomp_to_string cres2 in
                                   let uu____5442 =
                                     FStar_TypeChecker_Rel.guard_to_string
                                       env g in
                                   FStar_Util.print3
                                     "Not refining result: f=%s; cres=%s; guard=%s\n"
                                     uu____5440 uu____5441 uu____5442
                                 else ());
                                cres2) in
                           (cres3, g)
                       | uu____5444 ->
                           let g =
                             let uu____5449 =
                               FStar_TypeChecker_Rel.conj_guard ghead1 guard in
                             FStar_All.pipe_right uu____5449
                               (FStar_TypeChecker_Rel.solve_deferred_constraints
                                  env) in
                           let uu____5450 =
                             let uu____5451 =
                               let uu____5454 =
                                 let uu____5455 =
                                   let uu____5456 =
                                     cres1.FStar_Syntax_Syntax.comp () in
                                   FStar_Syntax_Util.arrow bs uu____5456 in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.subst subst1)
                                   uu____5455 in
                               FStar_Syntax_Syntax.mk_Total uu____5454 in
                             FStar_All.pipe_left
                               FStar_Syntax_Util.lcomp_of_comp uu____5451 in
                           (uu____5450, g) in
                     (match uu____5366 with
                      | (cres2,guard1) ->
                          ((let uu____5467 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Low in
                            if uu____5467
                            then
                              let uu____5468 =
                                FStar_Syntax_Print.lcomp_to_string cres2 in
                              FStar_Util.print1
                                "\t Type of result cres is %s\n" uu____5468
                            else ());
                           (let comp =
                              FStar_List.fold_left
                                (fun out_c  ->
                                   fun uu____5484  ->
                                     match uu____5484 with
                                     | ((e,q),x,c) ->
                                         (match c with
                                          | FStar_Util.Inl (eff_name,arg_typ)
                                              -> out_c
                                          | FStar_Util.Inr c1 ->
                                              FStar_TypeChecker_Util.bind
                                                e.FStar_Syntax_Syntax.pos env
                                                None c1 (x, out_c))) cres2
                                arg_comps_rev in
                            let comp1 =
                              FStar_TypeChecker_Util.bind
                                head2.FStar_Syntax_Syntax.pos env None chead1
                                (None, comp) in
                            let shortcuts_evaluation_order =
                              let uu____5530 =
                                let uu____5531 =
                                  FStar_Syntax_Subst.compress head2 in
                                uu____5531.FStar_Syntax_Syntax.n in
                              match uu____5530 with
                              | FStar_Syntax_Syntax.Tm_fvar fv ->
                                  (FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Syntax_Const.op_And)
                                    ||
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Syntax_Const.op_Or)
                              | uu____5535 -> false in
                            let app =
                              if shortcuts_evaluation_order
                              then
                                let args1 =
                                  FStar_List.fold_left
                                    (fun args1  ->
                                       fun uu____5549  ->
                                         match uu____5549 with
                                         | (arg,uu____5561,uu____5562) -> arg
                                             :: args1) [] arg_comps_rev in
                                let app =
                                  (FStar_Syntax_Syntax.mk_Tm_app head2 args1)
                                    (Some
                                       ((comp1.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                    r in
                                let app1 =
                                  FStar_TypeChecker_Util.maybe_lift env app
                                    cres2.FStar_Syntax_Syntax.eff_name
                                    comp1.FStar_Syntax_Syntax.eff_name
                                    comp1.FStar_Syntax_Syntax.res_typ in
                                FStar_TypeChecker_Util.maybe_monadic env app1
                                  comp1.FStar_Syntax_Syntax.eff_name
                                  comp1.FStar_Syntax_Syntax.res_typ
                              else
                                (let uu____5582 =
                                   let map_fun uu____5621 =
                                     match uu____5621 with
                                     | ((e,q),uu____5645,c0) ->
                                         (match c0 with
                                          | FStar_Util.Inl uu____5670 ->
                                              (None, (e, q))
                                          | FStar_Util.Inr c when
                                              FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                                c
                                              -> (None, (e, q))
                                          | FStar_Util.Inr c ->
                                              let x =
                                                FStar_Syntax_Syntax.new_bv
                                                  None
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let e1 =
                                                FStar_TypeChecker_Util.maybe_lift
                                                  env e
                                                  c.FStar_Syntax_Syntax.eff_name
                                                  comp1.FStar_Syntax_Syntax.eff_name
                                                  c.FStar_Syntax_Syntax.res_typ in
                                              let uu____5713 =
                                                let uu____5716 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    x in
                                                (uu____5716, q) in
                                              ((Some
                                                  (x,
                                                    (c.FStar_Syntax_Syntax.eff_name),
                                                    (c.FStar_Syntax_Syntax.res_typ),
                                                    e1)), uu____5713)) in
                                   let uu____5734 =
                                     let uu____5748 =
                                       let uu____5761 =
                                         let uu____5773 =
                                           let uu____5782 =
                                             FStar_Syntax_Syntax.as_arg head2 in
                                           (uu____5782, None,
                                             (FStar_Util.Inr chead1)) in
                                         uu____5773 :: arg_comps_rev in
                                       FStar_List.map map_fun uu____5761 in
                                     FStar_All.pipe_left FStar_List.split
                                       uu____5748 in
                                   match uu____5734 with
                                   | (lifted_args,reverse_args) ->
                                       let uu____5891 =
                                         let uu____5892 =
                                           FStar_List.hd reverse_args in
                                         Prims.fst uu____5892 in
                                       let uu____5897 =
                                         let uu____5901 =
                                           FStar_List.tl reverse_args in
                                         FStar_List.rev uu____5901 in
                                       (lifted_args, uu____5891, uu____5897) in
                                 match uu____5582 with
                                 | (lifted_args,head3,args1) ->
                                     let app =
                                       (FStar_Syntax_Syntax.mk_Tm_app head3
                                          args1)
                                         (Some
                                            ((comp1.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                         r in
                                     let app1 =
                                       FStar_TypeChecker_Util.maybe_lift env
                                         app
                                         cres2.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.res_typ in
                                     let app2 =
                                       FStar_TypeChecker_Util.maybe_monadic
                                         env app1
                                         comp1.FStar_Syntax_Syntax.eff_name
                                         comp1.FStar_Syntax_Syntax.res_typ in
                                     let bind_lifted_args e uu___85_5969 =
                                       match uu___85_5969 with
                                       | None  -> e
                                       | Some (x,m,t,e1) ->
                                           let lb =
                                             FStar_Syntax_Util.mk_letbinding
                                               (FStar_Util.Inl x) [] t m e1 in
                                           let letbinding =
                                             let uu____6011 =
                                               let uu____6014 =
                                                 let uu____6015 =
                                                   let uu____6023 =
                                                     let uu____6024 =
                                                       let uu____6025 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           x in
                                                       [uu____6025] in
                                                     FStar_Syntax_Subst.close
                                                       uu____6024 e in
                                                   ((false, [lb]),
                                                     uu____6023) in
                                                 FStar_Syntax_Syntax.Tm_let
                                                   uu____6015 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____6014 in
                                             uu____6011 None
                                               e.FStar_Syntax_Syntax.pos in
                                           (FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (letbinding,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      (m,
                                                        (comp1.FStar_Syntax_Syntax.res_typ))))))
                                             None e.FStar_Syntax_Syntax.pos in
                                     FStar_List.fold_left bind_lifted_args
                                       app2 lifted_args) in
                            let uu____6059 =
                              FStar_TypeChecker_Util.strengthen_precondition
                                None env app comp1 guard1 in
                            match uu____6059 with
                            | (comp2,g) -> (app, comp2, g)))) in
               let rec tc_args head_info uu____6117 bs args1 =
                 match uu____6117 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,Some (FStar_Syntax_Syntax.Implicit uu____6212))::rest,
                         (uu____6214,None )::uu____6215) ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort in
                          let t1 = check_no_escape (Some head1) env fvs t in
                          let uu____6252 =
                            FStar_TypeChecker_Util.new_implicit_var
                              "Instantiating implicit argument in application"
                              head1.FStar_Syntax_Syntax.pos env t1 in
                          (match uu____6252 with
                           | (varg,uu____6263,implicits) ->
                               let subst2 =
                                 (FStar_Syntax_Syntax.NT (x, varg)) :: subst1 in
                               let arg =
                                 let uu____6276 =
                                   FStar_Syntax_Syntax.as_implicit true in
                                 (varg, uu____6276) in
                               let uu____6277 =
                                 let uu____6299 =
                                   FStar_TypeChecker_Rel.conj_guard implicits
                                     g in
                                 (subst2,
                                   ((arg, None,
                                      (FStar_Util.Inl
                                         (FStar_Syntax_Const.effect_Tot_lid,
                                           t1))) :: outargs), (arg ::
                                   arg_rets), uu____6299, fvs) in
                               tc_args head_info uu____6277 rest args1)
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (Some (FStar_Syntax_Syntax.Implicit _),Some
                               (FStar_Syntax_Syntax.Implicit _))
                              |(None ,None )
                               |(Some (FStar_Syntax_Syntax.Equality ),None )
                                -> ()
                            | uu____6390 ->
                                Prims.raise
                                  (FStar_Errors.Error
                                     ("Inconsistent implicit qualifier",
                                       (e.FStar_Syntax_Syntax.pos))));
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort in
                            let x1 =
                              let uu___111_6397 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___111_6397.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___111_6397.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              } in
                            (let uu____6399 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme in
                             if uu____6399
                             then
                               let uu____6400 =
                                 FStar_Syntax_Print.term_to_string targ in
                               FStar_Util.print1
                                 "\tType of arg (after subst) = %s\n"
                                 uu____6400
                             else ());
                            (let targ1 =
                               check_no_escape (Some head1) env fvs targ in
                             let env1 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 targ1 in
                             let env2 =
                               let uu___112_6405 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___112_6405.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___112_6405.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___112_6405.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___112_6405.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___112_6405.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___112_6405.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___112_6405.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___112_6405.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___112_6405.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___112_6405.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___112_6405.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___112_6405.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___112_6405.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___112_6405.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___112_6405.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq = (is_eq aqual);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___112_6405.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___112_6405.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___112_6405.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___112_6405.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___112_6405.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___112_6405.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___112_6405.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___112_6405.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             (let uu____6407 =
                                FStar_TypeChecker_Env.debug env2
                                  FStar_Options.High in
                              if uu____6407
                              then
                                let uu____6408 =
                                  FStar_Syntax_Print.tag_of_term e in
                                let uu____6409 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____6410 =
                                  FStar_Syntax_Print.term_to_string targ1 in
                                FStar_Util.print3
                                  "Checking arg (%s) %s at type %s\n"
                                  uu____6408 uu____6409 uu____6410
                              else ());
                             (let uu____6412 = tc_term env2 e in
                              match uu____6412 with
                              | (e1,c,g_e) ->
                                  let g1 =
                                    FStar_TypeChecker_Rel.conj_guard g g_e in
                                  let arg = (e1, aq) in
                                  let uu____6428 =
                                    FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
                                  if uu____6428
                                  then
                                    let subst2 =
                                      let uu____6433 = FStar_List.hd bs in
                                      maybe_extend_subst subst1 uu____6433 e1 in
                                    tc_args head_info
                                      (subst2,
                                        ((arg, None,
                                           (FStar_Util.Inl
                                              ((c.FStar_Syntax_Syntax.eff_name),
                                                (c.FStar_Syntax_Syntax.res_typ))))
                                        :: outargs), (arg :: arg_rets), g1,
                                        fvs) rest rest'
                                  else
                                    (let uu____6489 =
                                       FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                         env2 c.FStar_Syntax_Syntax.eff_name in
                                     if uu____6489
                                     then
                                       let subst2 =
                                         let uu____6494 = FStar_List.hd bs in
                                         maybe_extend_subst subst1 uu____6494
                                           e1 in
                                       tc_args head_info
                                         (subst2,
                                           ((arg, (Some x1),
                                              (FStar_Util.Inr c)) ::
                                           outargs), (arg :: arg_rets), g1,
                                           fvs) rest rest'
                                     else
                                       (let uu____6540 =
                                          let uu____6541 = FStar_List.hd bs in
                                          FStar_Syntax_Syntax.is_null_binder
                                            uu____6541 in
                                        if uu____6540
                                        then
                                          let newx =
                                            FStar_Syntax_Syntax.new_bv
                                              (Some
                                                 (e1.FStar_Syntax_Syntax.pos))
                                              c.FStar_Syntax_Syntax.res_typ in
                                          let arg' =
                                            let uu____6550 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                newx in
                                            FStar_All.pipe_left
                                              FStar_Syntax_Syntax.as_arg
                                              uu____6550 in
                                          tc_args head_info
                                            (subst1,
                                              ((arg, (Some newx),
                                                 (FStar_Util.Inr c)) ::
                                              outargs), (arg' :: arg_rets),
                                              g1, fvs) rest rest'
                                        else
                                          (let uu____6588 =
                                             let uu____6610 =
                                               let uu____6612 =
                                                 let uu____6613 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     x1 in
                                                 FStar_Syntax_Syntax.as_arg
                                                   uu____6613 in
                                               uu____6612 :: arg_rets in
                                             (subst1,
                                               ((arg, (Some x1),
                                                  (FStar_Util.Inr c)) ::
                                               outargs), uu____6610, g1, (x1
                                               :: fvs)) in
                                           tc_args head_info uu____6588 rest
                                             rest')))))))
                      | (uu____6650,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____6671) ->
                          let uu____6701 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs [] in
                          (match uu____6701 with
                           | (head2,chead1,ghead1) ->
                               let rec aux norm1 tres =
                                 let tres1 =
                                   let uu____6724 =
                                     FStar_Syntax_Subst.compress tres in
                                   FStar_All.pipe_right uu____6724
                                     FStar_Syntax_Util.unrefine in
                                 match tres1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow (bs1,cres')
                                     ->
                                     let uu____6740 =
                                       FStar_Syntax_Subst.open_comp bs1 cres' in
                                     (match uu____6740 with
                                      | (bs2,cres'1) ->
                                          let head_info1 =
                                            (head2, chead1, ghead1,
                                              (FStar_Syntax_Util.lcomp_of_comp
                                                 cres'1)) in
                                          ((let uu____6754 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Low in
                                            if uu____6754
                                            then
                                              let uu____6755 =
                                                FStar_Range.string_of_range
                                                  tres1.FStar_Syntax_Syntax.pos in
                                              FStar_Util.print1
                                                "%s: Warning: Potentially redundant explicit currying of a function type \n"
                                                uu____6755
                                            else ());
                                           tc_args head_info1
                                             ([], [], [],
                                               FStar_TypeChecker_Rel.trivial_guard,
                                               []) bs2 args1))
                                 | uu____6785 when Prims.op_Negation norm1 ->
                                     let uu____6786 = unfold_whnf env tres1 in
                                     aux true uu____6786
                                 | uu____6787 ->
                                     let uu____6788 =
                                       let uu____6789 =
                                         let uu____6792 =
                                           let uu____6793 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env thead in
                                           let uu____6794 =
                                             FStar_Util.string_of_int n_args in
                                           FStar_Util.format2
                                             "Too many arguments to function of type %s; got %s arguments"
                                             uu____6793 uu____6794 in
                                         let uu____6798 =
                                           FStar_Syntax_Syntax.argpos arg in
                                         (uu____6792, uu____6798) in
                                       FStar_Errors.Error uu____6789 in
                                     Prims.raise uu____6788 in
                               aux false chead1.FStar_Syntax_Syntax.res_typ)) in
               let rec check_function_app norm1 tf =
                 let uu____6814 =
                   let uu____6815 = FStar_Syntax_Util.unrefine tf in
                   uu____6815.FStar_Syntax_Syntax.n in
                 match uu____6814 with
                 | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_)
                     ->
                     let rec tc_args1 env1 args1 =
                       match args1 with
                       | [] -> ([], [], FStar_TypeChecker_Rel.trivial_guard)
                       | (e,imp)::tl1 ->
                           let uu____6891 = tc_term env1 e in
                           (match uu____6891 with
                            | (e1,c,g_e) ->
                                let uu____6904 = tc_args1 env1 tl1 in
                                (match uu____6904 with
                                 | (args2,comps,g_rest) ->
                                     let uu____6926 =
                                       FStar_TypeChecker_Rel.conj_guard g_e
                                         g_rest in
                                     (((e1, imp) :: args2),
                                       (((e1.FStar_Syntax_Syntax.pos), c) ::
                                       comps), uu____6926))) in
                     let uu____6937 = tc_args1 env args in
                     (match uu____6937 with
                      | (args1,comps,g_args) ->
                          let bs =
                            let uu____6959 =
                              FStar_All.pipe_right comps
                                (FStar_List.map
                                   (fun uu____6979  ->
                                      match uu____6979 with
                                      | (uu____6987,c) ->
                                          ((c.FStar_Syntax_Syntax.res_typ),
                                            None))) in
                            FStar_Syntax_Util.null_binders_of_tks uu____6959 in
                          let ml_or_tot t r1 =
                            let uu____7003 = FStar_Options.ml_ish () in
                            if uu____7003
                            then FStar_Syntax_Util.ml_comp t r1
                            else FStar_Syntax_Syntax.mk_Total t in
                          let cres =
                            let uu____7006 =
                              let uu____7009 =
                                let uu____7010 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____7010 Prims.fst in
                              FStar_TypeChecker_Util.new_uvar env uu____7009 in
                            ml_or_tot uu____7006 r in
                          let bs_cres = FStar_Syntax_Util.arrow bs cres in
                          ((let uu____7019 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                FStar_Options.Extreme in
                            if uu____7019
                            then
                              let uu____7020 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____7021 =
                                FStar_Syntax_Print.term_to_string tf in
                              let uu____7022 =
                                FStar_Syntax_Print.term_to_string bs_cres in
                              FStar_Util.print3
                                "Forcing the type of %s from %s to %s\n"
                                uu____7020 uu____7021 uu____7022
                            else ());
                           (let uu____7025 =
                              FStar_TypeChecker_Rel.teq env tf bs_cres in
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Rel.force_trivial_guard env)
                              uu____7025);
                           (let comp =
                              let uu____7027 =
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp cres in
                              FStar_List.fold_right
                                (fun uu____7032  ->
                                   fun out  ->
                                     match uu____7032 with
                                     | (r1,c) ->
                                         FStar_TypeChecker_Util.bind r1 env
                                           None c (None, out))
                                (((head1.FStar_Syntax_Syntax.pos), chead) ::
                                comps) uu____7027 in
                            let uu____7041 =
                              (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                                (Some
                                   ((comp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                                r in
                            let uu____7048 =
                              FStar_TypeChecker_Rel.conj_guard ghead g_args in
                            (uu____7041, comp, uu____7048))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____7063 = FStar_Syntax_Subst.open_comp bs c in
                     (match uu____7063 with
                      | (bs1,c1) ->
                          let head_info =
                            (head1, chead, ghead,
                              (FStar_Syntax_Util.lcomp_of_comp c1)) in
                          tc_args head_info
                            ([], [], [], FStar_TypeChecker_Rel.trivial_guard,
                              []) bs1 args)
                 | uu____7106 ->
                     if Prims.op_Negation norm1
                     then
                       let uu____7112 = unfold_whnf env tf in
                       check_function_app true uu____7112
                     else
                       (let uu____7114 =
                          let uu____7115 =
                            let uu____7118 =
                              FStar_TypeChecker_Err.expected_function_typ env
                                tf in
                            (uu____7118, (head1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____7115 in
                        Prims.raise uu____7114) in
               let uu____7124 =
                 let uu____7125 = FStar_Syntax_Util.unrefine thead in
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.WHNF] env uu____7125 in
               check_function_app false uu____7124)
and check_short_circuit_args:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_TypeChecker_Env.guard_t ->
          ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) Prims.list
            ->
            FStar_Syntax_Syntax.typ Prims.option ->
              (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
                FStar_TypeChecker_Env.guard_t)
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
                  let uu____7171 =
                    FStar_List.fold_left2
                      (fun uu____7184  ->
                         fun uu____7185  ->
                           fun uu____7186  ->
                             match (uu____7184, uu____7185, uu____7186) with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 (if aq <> aq'
                                  then
                                    Prims.raise
                                      (FStar_Errors.Error
                                         ("Inconsistent implicit qualifiers",
                                           (e.FStar_Syntax_Syntax.pos)))
                                  else ();
                                  (let uu____7230 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort in
                                   match uu____7230 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen in
                                       let g1 =
                                         let uu____7242 =
                                           FStar_TypeChecker_Rel.guard_of_guard_formula
                                             short in
                                         FStar_TypeChecker_Rel.imp_guard
                                           uu____7242 g in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____7244 =
                                               FStar_Syntax_Util.is_total_lcomp
                                                 c1 in
                                             Prims.op_Negation uu____7244) &&
                                              (let uu____7245 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_Syntax_Syntax.eff_name in
                                               Prims.op_Negation uu____7245)) in
                                       let uu____7246 =
                                         let uu____7252 =
                                           let uu____7258 =
                                             FStar_Syntax_Syntax.as_arg e1 in
                                           [uu____7258] in
                                         FStar_List.append seen uu____7252 in
                                       let uu____7263 =
                                         FStar_TypeChecker_Rel.conj_guard
                                           guard g1 in
                                       (uu____7246, uu____7263, ghost1))))
                      ([], g_head, false) args bs in
                  (match uu____7171 with
                   | (args1,guard,ghost) ->
                       let e =
                         (FStar_Syntax_Syntax.mk_Tm_app head1 args1)
                           (Some (res_t.FStar_Syntax_Syntax.n)) r in
                       let c1 =
                         if ghost
                         then
                           let uu____7292 =
                             FStar_Syntax_Syntax.mk_GTotal res_t in
                           FStar_All.pipe_right uu____7292
                             FStar_Syntax_Util.lcomp_of_comp
                         else FStar_Syntax_Util.lcomp_of_comp c in
                       let uu____7294 =
                         FStar_TypeChecker_Util.strengthen_precondition None
                           env e c1 guard in
                       (match uu____7294 with | (c2,g) -> (e, c2, g)))
              | uu____7306 ->
                  check_application_args env head1 chead g_head args
                    expected_topt
and tc_eqn:
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.withinfo_t*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax) ->
        ((FStar_Syntax_Syntax.pat* FStar_Syntax_Syntax.term Prims.option*
          FStar_Syntax_Syntax.term)* FStar_Syntax_Syntax.term*
          FStar_Syntax_Syntax.lcomp* FStar_TypeChecker_Env.guard_t)
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____7328 = FStar_Syntax_Subst.open_branch branch1 in
        match uu____7328 with
        | (pattern,when_clause,branch_exp) ->
            let uu____7354 = branch1 in
            (match uu____7354 with
             | (cpat,uu____7374,cbr) ->
                 let tc_pat allow_implicits pat_t p0 =
                   let uu____7416 =
                     FStar_TypeChecker_Util.pat_as_exps allow_implicits env
                       p0 in
                   match uu____7416 with
                   | (pat_bvs1,exps,p) ->
                       ((let uu____7438 =
                           FStar_TypeChecker_Env.debug env FStar_Options.High in
                         if uu____7438
                         then
                           let uu____7439 =
                             FStar_Syntax_Print.pat_to_string p0 in
                           let uu____7440 =
                             FStar_Syntax_Print.pat_to_string p in
                           FStar_Util.print2 "Pattern %s elaborated to %s\n"
                             uu____7439 uu____7440
                         else ());
                        (let pat_env =
                           FStar_List.fold_left FStar_TypeChecker_Env.push_bv
                             env pat_bvs1 in
                         let uu____7443 =
                           FStar_TypeChecker_Env.clear_expected_typ pat_env in
                         match uu____7443 with
                         | (env1,uu____7456) ->
                             let env11 =
                               let uu___113_7460 = env1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___113_7460.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___113_7460.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___113_7460.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___113_7460.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___113_7460.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___113_7460.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___113_7460.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___113_7460.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern = true;
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___113_7460.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___113_7460.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___113_7460.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___113_7460.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___113_7460.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___113_7460.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___113_7460.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___113_7460.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___113_7460.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___113_7460.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___113_7460.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___113_7460.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___113_7460.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___113_7460.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___113_7460.FStar_TypeChecker_Env.qname_and_index)
                               } in
                             let expected_pat_t =
                               FStar_TypeChecker_Rel.unrefine env pat_t in
                             let uu____7462 =
                               let uu____7467 =
                                 FStar_All.pipe_right exps
                                   (FStar_List.map
                                      (fun e  ->
                                         (let uu____7479 =
                                            FStar_TypeChecker_Env.debug env
                                              FStar_Options.High in
                                          if uu____7479
                                          then
                                            let uu____7480 =
                                              FStar_Syntax_Print.term_to_string
                                                e in
                                            let uu____7481 =
                                              FStar_Syntax_Print.term_to_string
                                                pat_t in
                                            FStar_Util.print2
                                              "Checking pattern expression %s against expected type %s\n"
                                              uu____7480 uu____7481
                                          else ());
                                         (let uu____7483 = tc_term env11 e in
                                          match uu____7483 with
                                          | (e1,lc,g) ->
                                              ((let uu____7493 =
                                                  FStar_TypeChecker_Env.debug
                                                    env FStar_Options.High in
                                                if uu____7493
                                                then
                                                  let uu____7494 =
                                                    FStar_TypeChecker_Normalize.term_to_string
                                                      env e1 in
                                                  let uu____7495 =
                                                    FStar_TypeChecker_Normalize.term_to_string
                                                      env
                                                      lc.FStar_Syntax_Syntax.res_typ in
                                                  FStar_Util.print2
                                                    "Pre-checked pattern expression %s at type %s\n"
                                                    uu____7494 uu____7495
                                                else ());
                                               (let g' =
                                                  FStar_TypeChecker_Rel.teq
                                                    env
                                                    lc.FStar_Syntax_Syntax.res_typ
                                                    expected_pat_t in
                                                let g1 =
                                                  FStar_TypeChecker_Rel.conj_guard
                                                    g g' in
                                                let uu____7499 =
                                                  let uu____7500 =
                                                    FStar_TypeChecker_Rel.discharge_guard
                                                      env
                                                      (let uu___114_7501 = g1 in
                                                       {
                                                         FStar_TypeChecker_Env.guard_f
                                                           =
                                                           FStar_TypeChecker_Common.Trivial;
                                                         FStar_TypeChecker_Env.deferred
                                                           =
                                                           (uu___114_7501.FStar_TypeChecker_Env.deferred);
                                                         FStar_TypeChecker_Env.univ_ineqs
                                                           =
                                                           (uu___114_7501.FStar_TypeChecker_Env.univ_ineqs);
                                                         FStar_TypeChecker_Env.implicits
                                                           =
                                                           (uu___114_7501.FStar_TypeChecker_Env.implicits)
                                                       }) in
                                                  FStar_All.pipe_right
                                                    uu____7500
                                                    FStar_TypeChecker_Rel.resolve_implicits in
                                                let e' =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Normalize.Beta]
                                                    env e1 in
                                                let uvars_to_string uvs =
                                                  let uu____7515 =
                                                    let uu____7517 =
                                                      FStar_All.pipe_right
                                                        uvs
                                                        FStar_Util.set_elements in
                                                    FStar_All.pipe_right
                                                      uu____7517
                                                      (FStar_List.map
                                                         (fun uu____7541  ->
                                                            match uu____7541
                                                            with
                                                            | (u,uu____7546)
                                                                ->
                                                                FStar_Syntax_Print.uvar_to_string
                                                                  u)) in
                                                  FStar_All.pipe_right
                                                    uu____7515
                                                    (FStar_String.concat ", ") in
                                                let uvs1 =
                                                  FStar_Syntax_Free.uvars e' in
                                                let uvs2 =
                                                  FStar_Syntax_Free.uvars
                                                    expected_pat_t in
                                                (let uu____7559 =
                                                   let uu____7560 =
                                                     FStar_Util.set_is_subset_of
                                                       uvs1 uvs2 in
                                                   FStar_All.pipe_left
                                                     Prims.op_Negation
                                                     uu____7560 in
                                                 if uu____7559
                                                 then
                                                   let unresolved =
                                                     let uu____7567 =
                                                       FStar_Util.set_difference
                                                         uvs1 uvs2 in
                                                     FStar_All.pipe_right
                                                       uu____7567
                                                       FStar_Util.set_elements in
                                                   let uu____7581 =
                                                     let uu____7582 =
                                                       let uu____7585 =
                                                         let uu____7586 =
                                                           FStar_TypeChecker_Normalize.term_to_string
                                                             env e' in
                                                         let uu____7587 =
                                                           FStar_TypeChecker_Normalize.term_to_string
                                                             env
                                                             expected_pat_t in
                                                         let uu____7588 =
                                                           let uu____7589 =
                                                             FStar_All.pipe_right
                                                               unresolved
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____7601
                                                                     ->
                                                                    match uu____7601
                                                                    with
                                                                    | 
                                                                    (u,uu____7609)
                                                                    ->
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    u)) in
                                                           FStar_All.pipe_right
                                                             uu____7589
                                                             (FStar_String.concat
                                                                ", ") in
                                                         FStar_Util.format3
                                                           "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly"
                                                           uu____7586
                                                           uu____7587
                                                           uu____7588 in
                                                       (uu____7585,
                                                         (p.FStar_Syntax_Syntax.p)) in
                                                     FStar_Errors.Error
                                                       uu____7582 in
                                                   Prims.raise uu____7581
                                                 else ());
                                                (let uu____7624 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.High in
                                                 if uu____7624
                                                 then
                                                   let uu____7625 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env e1 in
                                                   FStar_Util.print1
                                                     "Done checking pattern expression %s\n"
                                                     uu____7625
                                                 else ());
                                                (e1, e')))))) in
                               FStar_All.pipe_right uu____7467
                                 FStar_List.unzip in
                             (match uu____7462 with
                              | (exps1,norm_exps) ->
                                  let p1 =
                                    FStar_TypeChecker_Util.decorate_pattern
                                      env p exps1 in
                                  (p1, pat_bvs1, pat_env, exps1, norm_exps)))) in
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee in
                 let uu____7656 =
                   let uu____7660 =
                     FStar_TypeChecker_Env.push_bv env scrutinee in
                   FStar_All.pipe_right uu____7660
                     FStar_TypeChecker_Env.clear_expected_typ in
                 (match uu____7656 with
                  | (scrutinee_env,uu____7673) ->
                      let uu____7676 = tc_pat true pat_t pattern in
                      (match uu____7676 with
                       | (pattern1,pat_bvs1,pat_env,disj_exps,norm_disj_exps)
                           ->
                           let uu____7704 =
                             match when_clause with
                             | None  ->
                                 (None, FStar_TypeChecker_Rel.trivial_guard)
                             | Some e ->
                                 let uu____7719 =
                                   FStar_TypeChecker_Env.should_verify env in
                                 if uu____7719
                                 then
                                   Prims.raise
                                     (FStar_Errors.Error
                                        ("When clauses are not yet supported in --verify mode; they will be some day",
                                          (e.FStar_Syntax_Syntax.pos)))
                                 else
                                   (let uu____7727 =
                                      let uu____7731 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env
                                          FStar_TypeChecker_Common.t_bool in
                                      tc_term uu____7731 e in
                                    match uu____7727 with
                                    | (e1,c,g) -> ((Some e1), g)) in
                           (match uu____7704 with
                            | (when_clause1,g_when) ->
                                let uu____7751 = tc_term pat_env branch_exp in
                                (match uu____7751 with
                                 | (branch_exp1,c,g_branch) ->
                                     let when_condition =
                                       match when_clause1 with
                                       | None  -> None
                                       | Some w ->
                                           let uu____7770 =
                                             FStar_Syntax_Util.mk_eq2
                                               FStar_Syntax_Syntax.U_zero
                                               FStar_Syntax_Util.t_bool w
                                               FStar_Syntax_Const.exp_true_bool in
                                           FStar_All.pipe_left
                                             (fun _0_30  -> Some _0_30)
                                             uu____7770 in
                                     let uu____7772 =
                                       let eqs =
                                         let uu____7778 =
                                           let uu____7779 =
                                             FStar_TypeChecker_Env.should_verify
                                               env in
                                           Prims.op_Negation uu____7779 in
                                         if uu____7778
                                         then None
                                         else
                                           FStar_All.pipe_right disj_exps
                                             (FStar_List.fold_left
                                                (fun fopt  ->
                                                   fun e  ->
                                                     let e1 =
                                                       FStar_Syntax_Subst.compress
                                                         e in
                                                     match e1.FStar_Syntax_Syntax.n
                                                     with
                                                     | FStar_Syntax_Syntax.Tm_uvar
                                                       _
                                                       |FStar_Syntax_Syntax.Tm_constant
                                                        _
                                                        |FStar_Syntax_Syntax.Tm_fvar
                                                        _ -> fopt
                                                     | uu____7793 ->
                                                         let clause =
                                                           let uu____7795 =
                                                             env.FStar_TypeChecker_Env.universe_of
                                                               env pat_t in
                                                           FStar_Syntax_Util.mk_eq2
                                                             uu____7795 pat_t
                                                             scrutinee_tm e1 in
                                                         (match fopt with
                                                          | None  ->
                                                              Some clause
                                                          | Some f ->
                                                              let uu____7798
                                                                =
                                                                FStar_Syntax_Util.mk_disj
                                                                  clause f in
                                                              FStar_All.pipe_left
                                                                (fun _0_31 
                                                                   ->
                                                                   Some _0_31)
                                                                uu____7798))
                                                None) in
                                       let uu____7808 =
                                         FStar_TypeChecker_Util.strengthen_precondition
                                           None env branch_exp1 c g_branch in
                                       match uu____7808 with
                                       | (c1,g_branch1) ->
                                           let uu____7818 =
                                             match (eqs, when_condition) with
                                             | uu____7825 when
                                                 let uu____7830 =
                                                   FStar_TypeChecker_Env.should_verify
                                                     env in
                                                 Prims.op_Negation uu____7830
                                                 -> (c1, g_when)
                                             | (None ,None ) -> (c1, g_when)
                                             | (Some f,None ) ->
                                                 let gf =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     gf in
                                                 let uu____7838 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 gf in
                                                 let uu____7839 =
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     g g_when in
                                                 (uu____7838, uu____7839)
                                             | (Some f,Some w) ->
                                                 let g_f =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     f in
                                                 let g_fw =
                                                   let uu____7846 =
                                                     FStar_Syntax_Util.mk_conj
                                                       f w in
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     uu____7846 in
                                                 let uu____7847 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_fw in
                                                 let uu____7848 =
                                                   let uu____7849 =
                                                     FStar_TypeChecker_Rel.guard_of_guard_formula
                                                       g_f in
                                                   FStar_TypeChecker_Rel.imp_guard
                                                     uu____7849 g_when in
                                                 (uu____7847, uu____7848)
                                             | (None ,Some w) ->
                                                 let g_w =
                                                   FStar_TypeChecker_Common.NonTrivial
                                                     w in
                                                 let g =
                                                   FStar_TypeChecker_Rel.guard_of_guard_formula
                                                     g_w in
                                                 let uu____7855 =
                                                   FStar_TypeChecker_Util.weaken_precondition
                                                     env c1 g_w in
                                                 (uu____7855, g_when) in
                                           (match uu____7818 with
                                            | (c_weak,g_when_weak) ->
                                                let binders =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1 in
                                                let uu____7863 =
                                                  FStar_TypeChecker_Util.close_comp
                                                    env pat_bvs1 c_weak in
                                                let uu____7864 =
                                                  FStar_TypeChecker_Rel.close_guard
                                                    binders g_when_weak in
                                                (uu____7863, uu____7864,
                                                  g_branch1)) in
                                     (match uu____7772 with
                                      | (c1,g_when1,g_branch1) ->
                                          let branch_guard =
                                            let uu____7877 =
                                              let uu____7878 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env in
                                              Prims.op_Negation uu____7878 in
                                            if uu____7877
                                            then FStar_Syntax_Util.t_true
                                            else
                                              (let rec build_branch_guard
                                                 scrutinee_tm1 pat_exp =
                                                 let discriminate
                                                   scrutinee_tm2 f =
                                                   let uu____7909 =
                                                     let uu____7910 =
                                                       let uu____7911 =
                                                         let uu____7913 =
                                                           let uu____7917 =
                                                             FStar_TypeChecker_Env.typ_of_datacon
                                                               env
                                                               f.FStar_Syntax_Syntax.v in
                                                           FStar_TypeChecker_Env.datacons_of_typ
                                                             env uu____7917 in
                                                         Prims.snd uu____7913 in
                                                       FStar_List.length
                                                         uu____7911 in
                                                     uu____7910 >
                                                       (Prims.parse_int "1") in
                                                   if uu____7909
                                                   then
                                                     let discriminator =
                                                       FStar_Syntax_Util.mk_discriminator
                                                         f.FStar_Syntax_Syntax.v in
                                                     let uu____7926 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env discriminator in
                                                     match uu____7926 with
                                                     | None  -> []
                                                     | uu____7937 ->
                                                         let disc =
                                                           FStar_Syntax_Syntax.fvar
                                                             discriminator
                                                             FStar_Syntax_Syntax.Delta_equational
                                                             None in
                                                         let disc1 =
                                                           let uu____7947 =
                                                             let uu____7948 =
                                                               let uu____7949
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   scrutinee_tm2 in
                                                               [uu____7949] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               disc
                                                               uu____7948 in
                                                           uu____7947 None
                                                             scrutinee_tm2.FStar_Syntax_Syntax.pos in
                                                         let uu____7954 =
                                                           FStar_Syntax_Util.mk_eq2
                                                             FStar_Syntax_Syntax.U_zero
                                                             FStar_Syntax_Util.t_bool
                                                             disc1
                                                             FStar_Syntax_Const.exp_true_bool in
                                                         [uu____7954]
                                                   else [] in
                                                 let fail uu____7962 =
                                                   let uu____7963 =
                                                     let uu____7964 =
                                                       FStar_Range.string_of_range
                                                         pat_exp.FStar_Syntax_Syntax.pos in
                                                     let uu____7965 =
                                                       FStar_Syntax_Print.term_to_string
                                                         pat_exp in
                                                     let uu____7966 =
                                                       FStar_Syntax_Print.tag_of_term
                                                         pat_exp in
                                                     FStar_Util.format3
                                                       "tc_eqn: Impossible (%s) %s (%s)"
                                                       uu____7964 uu____7965
                                                       uu____7966 in
                                                   failwith uu____7963 in
                                                 let rec head_constructor t =
                                                   match t.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv ->
                                                       fv.FStar_Syntax_Syntax.fv_name
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (t1,uu____7987) ->
                                                       head_constructor t1
                                                   | uu____7993 -> fail () in
                                                 let pat_exp1 =
                                                   let uu____7996 =
                                                     FStar_Syntax_Subst.compress
                                                       pat_exp in
                                                   FStar_All.pipe_right
                                                     uu____7996
                                                     FStar_Syntax_Util.unmeta in
                                                 match pat_exp1.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_uvar
                                                   _
                                                   |FStar_Syntax_Syntax.Tm_app
                                                    ({
                                                       FStar_Syntax_Syntax.n
                                                         =
                                                         FStar_Syntax_Syntax.Tm_uvar
                                                         _;
                                                       FStar_Syntax_Syntax.tk
                                                         = _;
                                                       FStar_Syntax_Syntax.pos
                                                         = _;
                                                       FStar_Syntax_Syntax.vars
                                                         = _;_},_)
                                                    |FStar_Syntax_Syntax.Tm_name
                                                     _
                                                     |FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     ) -> []
                                                 | FStar_Syntax_Syntax.Tm_constant
                                                     c2 ->
                                                     let uu____8013 =
                                                       let uu____8014 =
                                                         tc_constant
                                                           pat_exp1.FStar_Syntax_Syntax.pos
                                                           c2 in
                                                       FStar_Syntax_Util.mk_eq2
                                                         FStar_Syntax_Syntax.U_zero
                                                         uu____8014
                                                         scrutinee_tm1
                                                         pat_exp1 in
                                                     [uu____8013]
                                                 | FStar_Syntax_Syntax.Tm_uinst
                                                   _
                                                   |FStar_Syntax_Syntax.Tm_fvar
                                                   _ ->
                                                     let f =
                                                       head_constructor
                                                         pat_exp1 in
                                                     let uu____8022 =
                                                       let uu____8023 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8023 in
                                                     if uu____8022
                                                     then []
                                                     else
                                                       (let uu____8030 =
                                                          head_constructor
                                                            pat_exp1 in
                                                        discriminate
                                                          scrutinee_tm1
                                                          uu____8030)
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (head1,args) ->
                                                     let f =
                                                       head_constructor head1 in
                                                     let uu____8057 =
                                                       let uu____8058 =
                                                         FStar_TypeChecker_Env.is_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v in
                                                       Prims.op_Negation
                                                         uu____8058 in
                                                     if uu____8057
                                                     then []
                                                     else
                                                       (let sub_term_guards =
                                                          let uu____8067 =
                                                            FStar_All.pipe_right
                                                              args
                                                              (FStar_List.mapi
                                                                 (fun i  ->
                                                                    fun
                                                                    uu____8083
                                                                     ->
                                                                    match uu____8083
                                                                    with
                                                                    | 
                                                                    (ei,uu____8090)
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i in
                                                                    let uu____8100
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector in
                                                                    (match uu____8100
                                                                    with
                                                                    | 
                                                                    None  ->
                                                                    []
                                                                    | 
                                                                    uu____8111
                                                                    ->
                                                                    let sub_term
                                                                    =
                                                                    let uu____8120
                                                                    =
                                                                    let uu____8121
                                                                    =
                                                                    FStar_Syntax_Syntax.fvar
                                                                    (FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p)
                                                                    FStar_Syntax_Syntax.Delta_equational
                                                                    None in
                                                                    let uu____8126
                                                                    =
                                                                    let uu____8127
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm1 in
                                                                    [uu____8127] in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____8121
                                                                    uu____8126 in
                                                                    uu____8120
                                                                    None
                                                                    f.FStar_Syntax_Syntax.p in
                                                                    build_branch_guard
                                                                    sub_term
                                                                    ei))) in
                                                          FStar_All.pipe_right
                                                            uu____8067
                                                            FStar_List.flatten in
                                                        let uu____8139 =
                                                          discriminate
                                                            scrutinee_tm1 f in
                                                        FStar_List.append
                                                          uu____8139
                                                          sub_term_guards)
                                                 | uu____8143 -> [] in
                                               let build_and_check_branch_guard
                                                 scrutinee_tm1 pat =
                                                 let uu____8155 =
                                                   let uu____8156 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env in
                                                   Prims.op_Negation
                                                     uu____8156 in
                                                 if uu____8155
                                                 then
                                                   FStar_TypeChecker_Util.fvar_const
                                                     env
                                                     FStar_Syntax_Const.true_lid
                                                 else
                                                   (let t =
                                                      let uu____8159 =
                                                        build_branch_guard
                                                          scrutinee_tm1 pat in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.mk_conj_l
                                                        uu____8159 in
                                                    let uu____8162 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    match uu____8162 with
                                                    | (k,uu____8166) ->
                                                        let uu____8167 =
                                                          tc_check_tot_or_gtot_term
                                                            scrutinee_env t k in
                                                        (match uu____8167
                                                         with
                                                         | (t1,uu____8172,uu____8173)
                                                             -> t1)) in
                                               let branch_guard =
                                                 let uu____8175 =
                                                   FStar_All.pipe_right
                                                     norm_disj_exps
                                                     (FStar_List.map
                                                        (build_and_check_branch_guard
                                                           scrutinee_tm)) in
                                                 FStar_All.pipe_right
                                                   uu____8175
                                                   FStar_Syntax_Util.mk_disj_l in
                                               let branch_guard1 =
                                                 match when_condition with
                                                 | None  -> branch_guard
                                                 | Some w ->
                                                     FStar_Syntax_Util.mk_conj
                                                       branch_guard w in
                                               branch_guard1) in
                                          let guard =
                                            FStar_TypeChecker_Rel.conj_guard
                                              g_when1 g_branch1 in
                                          ((let uu____8186 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.High in
                                            if uu____8186
                                            then
                                              let uu____8187 =
                                                FStar_TypeChecker_Rel.guard_to_string
                                                  env guard in
                                              FStar_All.pipe_left
                                                (FStar_Util.print1
                                                   "Carrying guard from match: %s\n")
                                                uu____8187
                                            else ());
                                           (let uu____8189 =
                                              FStar_Syntax_Subst.close_branch
                                                (pattern1, when_clause1,
                                                  branch_exp1) in
                                            (uu____8189, branch_guard, c1,
                                              guard)))))))))
and check_top_level_let:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let uu____8207 = check_let_bound_def true env1 lb in
          (match uu____8207 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____8221 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then (g1, e1, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____8232 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1 in
                      FStar_All.pipe_right uu____8232
                        FStar_TypeChecker_Rel.resolve_implicits in
                    let uu____8234 =
                      let uu____8239 =
                        let uu____8245 =
                          let uu____8250 =
                            let uu____8258 = c1.FStar_Syntax_Syntax.comp () in
                            ((lb.FStar_Syntax_Syntax.lbname), e1, uu____8258) in
                          [uu____8250] in
                        FStar_TypeChecker_Util.generalize env1 uu____8245 in
                      FStar_List.hd uu____8239 in
                    match uu____8234 with
                    | (uu____8287,univs1,e11,c11) ->
                        (g11, e11, univs1,
                          (FStar_Syntax_Util.lcomp_of_comp c11))) in
               (match uu____8221 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____8298 =
                      let uu____8303 =
                        FStar_TypeChecker_Env.should_verify env1 in
                      if uu____8303
                      then
                        let uu____8308 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11 in
                        match uu____8308 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____8325 =
                                   FStar_Options.warn_top_level_effects () in
                                 if uu____8325
                                 then
                                   let uu____8326 =
                                     FStar_TypeChecker_Env.get_range env1 in
                                   FStar_Errors.warn uu____8326
                                     FStar_TypeChecker_Err.top_level_effect
                                 else ());
                                (let uu____8328 =
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_meta
                                         (e2,
                                           (FStar_Syntax_Syntax.Meta_desugared
                                              FStar_Syntax_Syntax.Masked_effect))))
                                     None e2.FStar_Syntax_Syntax.pos in
                                 (uu____8328, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let c =
                            let uu____8346 = c11.FStar_Syntax_Syntax.comp () in
                            FStar_All.pipe_right uu____8346
                              (FStar_TypeChecker_Normalize.normalize_comp
                                 [FStar_TypeChecker_Normalize.Beta] env1) in
                          let e21 =
                            let uu____8354 = FStar_Syntax_Util.is_pure_comp c in
                            if uu____8354
                            then e2
                            else
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_meta
                                    (e2,
                                      (FStar_Syntax_Syntax.Meta_desugared
                                         FStar_Syntax_Syntax.Masked_effect))))
                                None e2.FStar_Syntax_Syntax.pos in
                          (e21, c))) in
                    (match uu____8298 with
                     | (e21,c12) ->
                         let cres =
                           FStar_TypeChecker_Env.null_wp_for_eff env1
                             (FStar_Syntax_Util.comp_effect_name c12)
                             FStar_Syntax_Syntax.U_zero
                             FStar_TypeChecker_Common.t_unit in
                         (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                            (Some
                               (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                          (let lb1 =
                             FStar_Syntax_Util.close_univs_and_mk_letbinding
                               None lb.FStar_Syntax_Syntax.lbname univ_vars2
                               (FStar_Syntax_Util.comp_result c12)
                               (FStar_Syntax_Util.comp_effect_name c12) e11 in
                           let uu____8386 =
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21)))
                               (Some
                                  (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                               e.FStar_Syntax_Syntax.pos in
                           (uu____8386,
                             (FStar_Syntax_Util.lcomp_of_comp cres),
                             FStar_TypeChecker_Rel.trivial_guard))))))
      | uu____8405 -> failwith "Impossible"
and check_inner_let:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let env2 =
            let uu___115_8426 = env1 in
            {
              FStar_TypeChecker_Env.solver =
                (uu___115_8426.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___115_8426.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___115_8426.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___115_8426.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___115_8426.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___115_8426.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___115_8426.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___115_8426.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___115_8426.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___115_8426.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___115_8426.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___115_8426.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___115_8426.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___115_8426.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___115_8426.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___115_8426.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___115_8426.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___115_8426.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___115_8426.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.type_of =
                (uu___115_8426.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___115_8426.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___115_8426.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qname_and_index =
                (uu___115_8426.FStar_TypeChecker_Env.qname_and_index)
            } in
          let uu____8427 =
            let uu____8433 =
              let uu____8434 = FStar_TypeChecker_Env.clear_expected_typ env2 in
              FStar_All.pipe_right uu____8434 Prims.fst in
            check_let_bound_def false uu____8433 lb in
          (match uu____8427 with
           | (e1,uu____8446,c1,g1,annotated) ->
               let x =
                 let uu___116_8451 =
                   FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___116_8451.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___116_8451.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort =
                     (c1.FStar_Syntax_Syntax.res_typ)
                 } in
               let uu____8452 =
                 let uu____8455 =
                   let uu____8456 = FStar_Syntax_Syntax.mk_binder x in
                   [uu____8456] in
                 FStar_Syntax_Subst.open_term uu____8455 e2 in
               (match uu____8452 with
                | (xb,e21) ->
                    let xbinder = FStar_List.hd xb in
                    let x1 = Prims.fst xbinder in
                    let uu____8468 =
                      let uu____8472 = FStar_TypeChecker_Env.push_bv env2 x1 in
                      tc_term uu____8472 e21 in
                    (match uu____8468 with
                     | (e22,c2,g2) ->
                         let cres =
                           FStar_TypeChecker_Util.bind
                             e1.FStar_Syntax_Syntax.pos env2 (Some e1) c1
                             ((Some x1), c2) in
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
                           let uu____8487 =
                             let uu____8490 =
                               let uu____8491 =
                                 let uu____8499 =
                                   FStar_Syntax_Subst.close xb e23 in
                                 ((false, [lb1]), uu____8499) in
                               FStar_Syntax_Syntax.Tm_let uu____8491 in
                             FStar_Syntax_Syntax.mk uu____8490 in
                           uu____8487
                             (Some
                                ((cres.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n))
                             e.FStar_Syntax_Syntax.pos in
                         let e4 =
                           FStar_TypeChecker_Util.maybe_monadic env2 e3
                             cres.FStar_Syntax_Syntax.eff_name
                             cres.FStar_Syntax_Syntax.res_typ in
                         let x_eq_e1 =
                           let uu____8514 =
                             let uu____8515 =
                               env2.FStar_TypeChecker_Env.universe_of env2
                                 c1.FStar_Syntax_Syntax.res_typ in
                             let uu____8516 =
                               FStar_Syntax_Syntax.bv_to_name x1 in
                             FStar_Syntax_Util.mk_eq2 uu____8515
                               c1.FStar_Syntax_Syntax.res_typ uu____8516 e11 in
                           FStar_All.pipe_left
                             (fun _0_32  ->
                                FStar_TypeChecker_Common.NonTrivial _0_32)
                             uu____8514 in
                         let g21 =
                           let uu____8518 =
                             let uu____8519 =
                               FStar_TypeChecker_Rel.guard_of_guard_formula
                                 x_eq_e1 in
                             FStar_TypeChecker_Rel.imp_guard uu____8519 g2 in
                           FStar_TypeChecker_Rel.close_guard xb uu____8518 in
                         let guard = FStar_TypeChecker_Rel.conj_guard g1 g21 in
                         let uu____8521 =
                           let uu____8522 =
                             FStar_TypeChecker_Env.expected_typ env2 in
                           FStar_Option.isSome uu____8522 in
                         if uu____8521
                         then
                           let tt =
                             let uu____8528 =
                               FStar_TypeChecker_Env.expected_typ env2 in
                             FStar_All.pipe_right uu____8528 FStar_Option.get in
                           ((let uu____8532 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8532
                             then
                               let uu____8533 =
                                 FStar_Syntax_Print.term_to_string tt in
                               let uu____8534 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               FStar_Util.print2
                                 "Got expected type from env %s\ncres.res_typ=%s\n"
                                 uu____8533 uu____8534
                             else ());
                            (e4, cres, guard))
                         else
                           (let t =
                              check_no_escape None env2 [x1]
                                cres.FStar_Syntax_Syntax.res_typ in
                            (let uu____8539 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env2)
                                 (FStar_Options.Other "Exports") in
                             if uu____8539
                             then
                               let uu____8540 =
                                 FStar_Syntax_Print.term_to_string
                                   cres.FStar_Syntax_Syntax.res_typ in
                               let uu____8541 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Util.print2
                                 "Checked %s has no escaping types; normalized to %s\n"
                                 uu____8540 uu____8541
                             else ());
                            (e4,
                              ((let uu___117_8543 = cres in
                                {
                                  FStar_Syntax_Syntax.eff_name =
                                    (uu___117_8543.FStar_Syntax_Syntax.eff_name);
                                  FStar_Syntax_Syntax.res_typ = t;
                                  FStar_Syntax_Syntax.cflags =
                                    (uu___117_8543.FStar_Syntax_Syntax.cflags);
                                  FStar_Syntax_Syntax.comp =
                                    (uu___117_8543.FStar_Syntax_Syntax.comp)
                                })), guard)))))
      | uu____8544 -> failwith "Impossible"
and check_top_level_let_rec:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____8565 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____8565 with
           | (lbs1,e21) ->
               let uu____8576 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____8576 with
                | (env0,topt) ->
                    let uu____8587 = build_let_rec_env true env0 lbs1 in
                    (match uu____8587 with
                     | (lbs2,rec_env) ->
                         let uu____8598 = check_let_recs rec_env lbs2 in
                         (match uu____8598 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____8610 =
                                  FStar_TypeChecker_Rel.solve_deferred_constraints
                                    env1 g_lbs in
                                FStar_All.pipe_right uu____8610
                                  FStar_TypeChecker_Rel.resolve_implicits in
                              let all_lb_names =
                                let uu____8614 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname)) in
                                FStar_All.pipe_right uu____8614
                                  (fun _0_33  -> Some _0_33) in
                              let lbs4 =
                                if
                                  Prims.op_Negation
                                    env1.FStar_TypeChecker_Env.generalize
                                then
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
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
                                              lb.FStar_Syntax_Syntax.lbdef))
                                else
                                  (let ecs =
                                     let uu____8638 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____8660 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____8660))) in
                                     FStar_TypeChecker_Util.generalize env1
                                       uu____8638 in
                                   FStar_All.pipe_right ecs
                                     (FStar_List.map
                                        (fun uu____8680  ->
                                           match uu____8680 with
                                           | (x,uvs,e,c) ->
                                               FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                 all_lb_names x uvs
                                                 (FStar_Syntax_Util.comp_result
                                                    c)
                                                 (FStar_Syntax_Util.comp_effect_name
                                                    c) e))) in
                              let cres =
                                let uu____8705 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_TypeChecker_Common.t_unit in
                                FStar_All.pipe_left
                                  FStar_Syntax_Util.lcomp_of_comp uu____8705 in
                              (FStar_ST.write e21.FStar_Syntax_Syntax.tk
                                 (Some
                                    (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n));
                               (let uu____8714 =
                                  FStar_Syntax_Subst.close_let_rec lbs4 e21 in
                                match uu____8714 with
                                | (lbs5,e22) ->
                                    let uu____8725 =
                                      (FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22)))
                                        (Some
                                           (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n))
                                        top.FStar_Syntax_Syntax.pos in
                                    let uu____8740 =
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env1 g_lbs1 in
                                    (uu____8725, cres, uu____8740)))))))
      | uu____8743 -> failwith "Impossible"
and check_inner_let_rec:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____8764 = FStar_Syntax_Subst.open_let_rec lbs e2 in
          (match uu____8764 with
           | (lbs1,e21) ->
               let uu____8775 = FStar_TypeChecker_Env.clear_expected_typ env1 in
               (match uu____8775 with
                | (env0,topt) ->
                    let uu____8786 = build_let_rec_env false env0 lbs1 in
                    (match uu____8786 with
                     | (lbs2,rec_env) ->
                         let uu____8797 = check_let_recs rec_env lbs2 in
                         (match uu____8797 with
                          | (lbs3,g_lbs) ->
                              let uu____8808 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___118_8819 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___118_8819.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___118_8819.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            } in
                                          let lb1 =
                                            let uu___119_8821 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___119_8821.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___119_8821.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___119_8821.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___119_8821.FStar_Syntax_Syntax.lbdef)
                                            } in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp)) in
                                          (env3, lb1)) env1) in
                              (match uu____8808 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname)) in
                                   let uu____8838 = tc_term env2 e21 in
                                   (match uu____8838 with
                                    | (e22,cres,g2) ->
                                        let guard =
                                          let uu____8849 =
                                            let uu____8850 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs in
                                            FStar_TypeChecker_Rel.close_guard
                                              uu____8850 g2 in
                                          FStar_TypeChecker_Rel.conj_guard
                                            g_lbs uu____8849 in
                                        let cres1 =
                                          FStar_TypeChecker_Util.close_comp
                                            env2 bvs cres in
                                        let tres =
                                          norm env2
                                            cres1.FStar_Syntax_Syntax.res_typ in
                                        let cres2 =
                                          let uu___120_8854 = cres1 in
                                          {
                                            FStar_Syntax_Syntax.eff_name =
                                              (uu___120_8854.FStar_Syntax_Syntax.eff_name);
                                            FStar_Syntax_Syntax.res_typ =
                                              tres;
                                            FStar_Syntax_Syntax.cflags =
                                              (uu___120_8854.FStar_Syntax_Syntax.cflags);
                                            FStar_Syntax_Syntax.comp =
                                              (uu___120_8854.FStar_Syntax_Syntax.comp)
                                          } in
                                        let uu____8855 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22 in
                                        (match uu____8855 with
                                         | (lbs5,e23) ->
                                             let e =
                                               (FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_let
                                                     ((true, lbs5), e23)))
                                                 (Some
                                                    (tres.FStar_Syntax_Syntax.n))
                                                 top.FStar_Syntax_Syntax.pos in
                                             (match topt with
                                              | Some uu____8884 ->
                                                  (e, cres2, guard)
                                              | None  ->
                                                  let tres1 =
                                                    check_no_escape None env2
                                                      bvs tres in
                                                  let cres3 =
                                                    let uu___121_8889 = cres2 in
                                                    {
                                                      FStar_Syntax_Syntax.eff_name
                                                        =
                                                        (uu___121_8889.FStar_Syntax_Syntax.eff_name);
                                                      FStar_Syntax_Syntax.res_typ
                                                        = tres1;
                                                      FStar_Syntax_Syntax.cflags
                                                        =
                                                        (uu___121_8889.FStar_Syntax_Syntax.cflags);
                                                      FStar_Syntax_Syntax.comp
                                                        =
                                                        (uu___121_8889.FStar_Syntax_Syntax.comp)
                                                    } in
                                                  (e, cres3, guard)))))))))
      | uu____8892 -> failwith "Impossible"
and build_let_rec_env:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list*
          FStar_TypeChecker_Env.env_t)
  =
  fun top_level  ->
    fun env  ->
      fun lbs  ->
        let env0 = env in
        let termination_check_enabled t =
          let uu____8908 = FStar_Syntax_Util.arrow_formals_comp t in
          match uu____8908 with
          | (uu____8914,c) ->
              let quals =
                FStar_TypeChecker_Env.lookup_effect_quals env
                  (FStar_Syntax_Util.comp_effect_name c) in
              FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.TotalEffect) in
        let uu____8925 =
          FStar_List.fold_left
            (fun uu____8932  ->
               fun lb  ->
                 match uu____8932 with
                 | (lbs1,env1) ->
                     let uu____8944 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb in
                     (match uu____8944 with
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
                              (let uu____8958 =
                                 let uu____8962 =
                                   let uu____8963 =
                                     FStar_Syntax_Util.type_u () in
                                   FStar_All.pipe_left Prims.fst uu____8963 in
                                 tc_check_tot_or_gtot_term
                                   (let uu___122_8968 = env0 in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___122_8968.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___122_8968.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___122_8968.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___122_8968.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___122_8968.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___122_8968.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___122_8968.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___122_8968.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___122_8968.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___122_8968.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___122_8968.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___122_8968.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___122_8968.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___122_8968.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___122_8968.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___122_8968.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___122_8968.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___122_8968.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___122_8968.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___122_8968.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___122_8968.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___122_8968.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qname_and_index =
                                        (uu___122_8968.FStar_TypeChecker_Env.qname_and_index)
                                    }) t uu____8962 in
                               match uu____8958 with
                               | (t1,uu____8970,g) ->
                                   let g1 =
                                     FStar_TypeChecker_Rel.resolve_implicits
                                       g in
                                   ((let uu____8974 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env2 g1 in
                                     FStar_All.pipe_left Prims.ignore
                                       uu____8974);
                                    norm env0 t1)) in
                          let env3 =
                            let uu____8976 =
                              (termination_check_enabled t1) &&
                                (FStar_TypeChecker_Env.should_verify env2) in
                            if uu____8976
                            then
                              let uu___123_8977 = env2 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___123_8977.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___123_8977.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___123_8977.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___123_8977.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___123_8977.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___123_8977.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___123_8977.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___123_8977.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___123_8977.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___123_8977.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___123_8977.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___123_8977.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (((lb.FStar_Syntax_Syntax.lbname), t1) ::
                                  (env2.FStar_TypeChecker_Env.letrecs));
                                FStar_TypeChecker_Env.top_level =
                                  (uu___123_8977.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___123_8977.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___123_8977.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___123_8977.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___123_8977.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax =
                                  (uu___123_8977.FStar_TypeChecker_Env.lax);
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___123_8977.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___123_8977.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___123_8977.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___123_8977.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___123_8977.FStar_TypeChecker_Env.qname_and_index)
                              }
                            else
                              FStar_TypeChecker_Env.push_let_binding env2
                                lb.FStar_Syntax_Syntax.lbname ([], t1) in
                          let lb1 =
                            let uu___124_8987 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___124_8987.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs = univ_vars1;
                              FStar_Syntax_Syntax.lbtyp = t1;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___124_8987.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = e
                            } in
                          ((lb1 :: lbs1), env3))) ([], env) lbs in
        match uu____8925 with | (lbs1,env1) -> ((FStar_List.rev lbs1), env1)
and check_let_recs:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun lbs  ->
      let uu____9001 =
        let uu____9006 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____9017 =
                    let uu____9021 =
                      FStar_TypeChecker_Env.set_expected_typ env
                        lb.FStar_Syntax_Syntax.lbtyp in
                    tc_tot_or_gtot_term uu____9021
                      lb.FStar_Syntax_Syntax.lbdef in
                  match uu____9017 with
                  | (e,c,g) ->
                      ((let uu____9028 =
                          let uu____9029 = FStar_Syntax_Util.is_total_lcomp c in
                          Prims.op_Negation uu____9029 in
                        if uu____9028
                        then
                          Prims.raise
                            (FStar_Errors.Error
                               ("Expected let rec to be a Tot term; got effect GTot",
                                 (e.FStar_Syntax_Syntax.pos)))
                        else ());
                       (let lb1 =
                          FStar_Syntax_Util.mk_letbinding
                            lb.FStar_Syntax_Syntax.lbname
                            lb.FStar_Syntax_Syntax.lbunivs
                            lb.FStar_Syntax_Syntax.lbtyp
                            FStar_Syntax_Const.effect_Tot_lid e in
                        (lb1, g))))) in
        FStar_All.pipe_right uu____9006 FStar_List.unzip in
      match uu____9001 with
      | (lbs1,gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs
              FStar_TypeChecker_Rel.trivial_guard in
          (lbs1, g_lbs)
and check_let_bound_def:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.univ_names*
          FStar_Syntax_Syntax.lcomp* FStar_TypeChecker_Env.guard_t*
          Prims.bool)
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let uu____9058 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____9058 with
        | (env1,uu____9068) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef in
            let uu____9074 = check_lbtyp top_level env lb in
            (match uu____9074 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    Prims.raise
                      (FStar_Errors.Error
                         ("Inner let-bound definitions cannot be universe polymorphic",
                           (e1.FStar_Syntax_Syntax.pos)))
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1 in
                   let uu____9100 =
                     tc_maybe_toplevel_term
                       (let uu___125_9104 = env11 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___125_9104.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___125_9104.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___125_9104.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___125_9104.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___125_9104.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___125_9104.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___125_9104.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___125_9104.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___125_9104.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___125_9104.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___125_9104.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___125_9104.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___125_9104.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___125_9104.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___125_9104.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___125_9104.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___125_9104.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___125_9104.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___125_9104.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.type_of =
                            (uu___125_9104.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___125_9104.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___125_9104.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___125_9104.FStar_TypeChecker_Env.qname_and_index)
                        }) e11 in
                   match uu____9100 with
                   | (e12,c1,g1) ->
                       let uu____9113 =
                         let uu____9116 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (Some
                              (fun uu____9119  ->
                                 FStar_TypeChecker_Err.ill_kinded_type))
                           uu____9116 e12 c1 wf_annot in
                       (match uu____9113 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Rel.conj_guard g1 guard_f in
                            ((let uu____9129 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme in
                              if uu____9129
                              then
                                let uu____9130 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname in
                                let uu____9131 =
                                  FStar_Syntax_Print.term_to_string
                                    c11.FStar_Syntax_Syntax.res_typ in
                                let uu____9132 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11 in
                                FStar_Util.print3
                                  "checked top-level def %s, result type is %s, guard is %s\n"
                                  uu____9130 uu____9131 uu____9132
                              else ());
                             (e12, univ_vars1, c11, g11,
                               (FStar_Option.isSome topt)))))))
and check_lbtyp:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ Prims.option* FStar_TypeChecker_Env.guard_t*
          FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.subst_elt
          Prims.list* FStar_TypeChecker_Env.env)
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
             (None, FStar_TypeChecker_Rel.trivial_guard, [], [], env))
        | uu____9158 ->
            let uu____9159 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs in
            (match uu____9159 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1 in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____9186 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1 in
                   ((Some t1), FStar_TypeChecker_Rel.trivial_guard,
                     univ_vars1, univ_opening, uu____9186)
                 else
                   (let uu____9191 = FStar_Syntax_Util.type_u () in
                    match uu____9191 with
                    | (k,uu____9202) ->
                        let uu____9203 = tc_check_tot_or_gtot_term env1 t1 k in
                        (match uu____9203 with
                         | (t2,uu____9215,g) ->
                             ((let uu____9218 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium in
                               if uu____9218
                               then
                                 let uu____9219 =
                                   let uu____9220 =
                                     FStar_Syntax_Syntax.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname in
                                   FStar_Range.string_of_range uu____9220 in
                                 let uu____9221 =
                                   FStar_Syntax_Print.term_to_string t2 in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____9219 uu____9221
                               else ());
                              (let t3 = norm env1 t2 in
                               let uu____9224 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3 in
                               ((Some t3), g, univ_vars1, univ_opening,
                                 uu____9224))))))
and tc_binder:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) ->
      ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)*
        FStar_TypeChecker_Env.env* FStar_TypeChecker_Env.guard_t*
        FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun uu____9229  ->
      match uu____9229 with
      | (x,imp) ->
          let uu____9240 = FStar_Syntax_Util.type_u () in
          (match uu____9240 with
           | (tu,u) ->
               ((let uu____9252 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme in
                 if uu____9252
                 then
                   let uu____9253 = FStar_Syntax_Print.bv_to_string x in
                   let uu____9254 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort in
                   let uu____9255 = FStar_Syntax_Print.term_to_string tu in
                   FStar_Util.print3 "Checking binders %s:%s at type %s\n"
                     uu____9253 uu____9254 uu____9255
                 else ());
                (let uu____9257 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu in
                 match uu____9257 with
                 | (t,uu____9268,g) ->
                     let x1 =
                       ((let uu___126_9273 = x in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___126_9273.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___126_9273.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t
                         }), imp) in
                     ((let uu____9275 =
                         FStar_TypeChecker_Env.debug env FStar_Options.High in
                       if uu____9275
                       then
                         let uu____9276 =
                           FStar_Syntax_Print.bv_to_string (Prims.fst x1) in
                         let uu____9277 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.print2 "Pushing binder %s at type %s\n"
                           uu____9276 uu____9277
                       else ());
                      (let uu____9279 = push_binding env x1 in
                       (x1, uu____9279, g, u))))))
and tc_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list*
        FStar_TypeChecker_Env.env* FStar_TypeChecker_Env.guard_t*
        FStar_Syntax_Syntax.universe Prims.list)
  =
  fun env  ->
    fun bs  ->
      let rec aux env1 bs1 =
        match bs1 with
        | [] -> ([], env1, FStar_TypeChecker_Rel.trivial_guard, [])
        | b::bs2 ->
            let uu____9330 = tc_binder env1 b in
            (match uu____9330 with
             | (b1,env',g,u) ->
                 let uu____9353 = aux env' bs2 in
                 (match uu____9353 with
                  | (bs3,env'1,g',us) ->
                      let uu____9382 =
                        let uu____9383 =
                          FStar_TypeChecker_Rel.close_guard [b1] g' in
                        FStar_TypeChecker_Rel.conj_guard g uu____9383 in
                      ((b1 :: bs3), env'1, uu____9382, (u :: us)))) in
      aux env bs
and tc_pats:
  FStar_TypeChecker_Env.env ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) Prims.list
      Prims.list ->
      (FStar_Syntax_Syntax.args Prims.list* FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun pats  ->
      let tc_args env1 args =
        FStar_List.fold_right
          (fun uu____9426  ->
             fun uu____9427  ->
               match (uu____9426, uu____9427) with
               | ((t,imp),(args1,g)) ->
                   let uu____9464 = tc_term env1 t in
                   (match uu____9464 with
                    | (t1,uu____9474,g') ->
                        let uu____9476 =
                          FStar_TypeChecker_Rel.conj_guard g g' in
                        (((t1, imp) :: args1), uu____9476))) args
          ([], FStar_TypeChecker_Rel.trivial_guard) in
      FStar_List.fold_right
        (fun p  ->
           fun uu____9494  ->
             match uu____9494 with
             | (pats1,g) ->
                 let uu____9508 = tc_args env p in
                 (match uu____9508 with
                  | (args,g') ->
                      let uu____9516 = FStar_TypeChecker_Rel.conj_guard g g' in
                      ((args :: pats1), uu____9516))) pats
        ([], FStar_TypeChecker_Rel.trivial_guard)
and tc_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      let uu____9524 = tc_maybe_toplevel_term env e in
      match uu____9524 with
      | (e1,c,g) ->
          let uu____9534 = FStar_Syntax_Util.is_tot_or_gtot_lcomp c in
          if uu____9534
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g in
             let c1 = c.FStar_Syntax_Syntax.comp () in
             let c2 = norm_c env c1 in
             let uu____9544 =
               let uu____9547 =
                 FStar_TypeChecker_Util.is_pure_effect env
                   (FStar_Syntax_Util.comp_effect_name c2) in
               if uu____9547
               then
                 let uu____9550 =
                   FStar_Syntax_Syntax.mk_Total
                     (FStar_Syntax_Util.comp_result c2) in
                 (uu____9550, false)
               else
                 (let uu____9552 =
                    FStar_Syntax_Syntax.mk_GTotal
                      (FStar_Syntax_Util.comp_result c2) in
                  (uu____9552, true)) in
             match uu____9544 with
             | (target_comp,allow_ghost) ->
                 let uu____9558 =
                   FStar_TypeChecker_Rel.sub_comp env c2 target_comp in
                 (match uu____9558 with
                  | Some g' ->
                      let uu____9564 = FStar_TypeChecker_Rel.conj_guard g1 g' in
                      (e1, (FStar_Syntax_Util.lcomp_of_comp target_comp),
                        uu____9564)
                  | uu____9565 ->
                      if allow_ghost
                      then
                        let uu____9570 =
                          let uu____9571 =
                            let uu____9574 =
                              FStar_TypeChecker_Err.expected_ghost_expression
                                e1 c2 in
                            (uu____9574, (e1.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____9571 in
                        Prims.raise uu____9570
                      else
                        (let uu____9579 =
                           let uu____9580 =
                             let uu____9583 =
                               FStar_TypeChecker_Err.expected_pure_expression
                                 e1 c2 in
                             (uu____9583, (e1.FStar_Syntax_Syntax.pos)) in
                           FStar_Errors.Error uu____9580 in
                         Prims.raise uu____9579)))
and tc_check_tot_or_gtot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp*
          FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let env1 = FStar_TypeChecker_Env.set_expected_typ env t in
        tc_tot_or_gtot_term env1 e
and tc_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun t  ->
      let uu____9596 = tc_tot_or_gtot_term env t in
      match uu____9596 with
      | (t1,c,g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))
let type_of_tot_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.typ*
        FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun e  ->
      (let uu____9616 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9616
       then
         let uu____9617 = FStar_Syntax_Print.term_to_string e in
         FStar_Util.print1 "Checking term %s\n" uu____9617
       else ());
      (let env1 =
         let uu___127_9620 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___127_9620.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___127_9620.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___127_9620.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___127_9620.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___127_9620.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___127_9620.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___127_9620.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___127_9620.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___127_9620.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___127_9620.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___127_9620.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___127_9620.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___127_9620.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___127_9620.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___127_9620.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___127_9620.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___127_9620.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___127_9620.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___127_9620.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___127_9620.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts = true;
           FStar_TypeChecker_Env.qname_and_index =
             (uu___127_9620.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____9623 =
         try tc_tot_or_gtot_term env1 e
         with
         | FStar_Errors.Error (msg,uu____9639) ->
             let uu____9640 =
               let uu____9641 =
                 let uu____9644 = FStar_TypeChecker_Env.get_range env1 in
                 ((Prims.strcat "Implicit argument: " msg), uu____9644) in
               FStar_Errors.Error uu____9641 in
             Prims.raise uu____9640 in
       match uu____9623 with
       | (t,c,g) ->
           let uu____9654 = FStar_Syntax_Util.is_total_lcomp c in
           if uu____9654
           then (t, (c.FStar_Syntax_Syntax.res_typ), g)
           else
             (let uu____9661 =
                let uu____9662 =
                  let uu____9665 =
                    let uu____9666 = FStar_Syntax_Print.term_to_string e in
                    FStar_Util.format1
                      "Implicit argument: Expected a total term; got a ghost term: %s"
                      uu____9666 in
                  let uu____9667 = FStar_TypeChecker_Env.get_range env1 in
                  (uu____9665, uu____9667) in
                FStar_Errors.Error uu____9662 in
              Prims.raise uu____9661))
let level_of_type_fail env e t =
  let uu____9688 =
    let uu____9689 =
      let uu____9692 =
        let uu____9693 = FStar_Syntax_Print.term_to_string e in
        FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
          uu____9693 t in
      let uu____9694 = FStar_TypeChecker_Env.get_range env in
      (uu____9692, uu____9694) in
    FStar_Errors.Error uu____9689 in
  Prims.raise uu____9688
let level_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____9711 =
            let uu____9712 = FStar_Syntax_Util.unrefine t1 in
            uu____9712.FStar_Syntax_Syntax.n in
          match uu____9711 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____9716 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.UnfoldUntil
                       FStar_Syntax_Syntax.Delta_constant] env t1 in
                aux false t2
              else
                (let uu____9719 = FStar_Syntax_Util.type_u () in
                 match uu____9719 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___130_9725 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___130_9725.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___130_9725.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___130_9725.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___130_9725.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___130_9725.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___130_9725.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___130_9725.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___130_9725.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___130_9725.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___130_9725.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___130_9725.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___130_9725.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___130_9725.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___130_9725.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___130_9725.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___130_9725.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___130_9725.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___130_9725.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___130_9725.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___130_9725.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___130_9725.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___130_9725.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___130_9725.FStar_TypeChecker_Env.qname_and_index)
                       } in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u in
                     ((match g.FStar_TypeChecker_Env.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____9729 =
                             FStar_Syntax_Print.term_to_string t1 in
                           level_of_type_fail env1 e uu____9729
                       | uu____9730 ->
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
      let uu____9739 =
        let uu____9740 = FStar_Syntax_Subst.compress e in
        uu____9740.FStar_Syntax_Syntax.n in
      match uu____9739 with
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_delayed _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____9749 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____9760) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (uu____9785,t) -> t
      | FStar_Syntax_Syntax.Tm_meta (t,uu____9800) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____9807 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____9807 with | ((uu____9818,t),uu____9820) -> t)
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____9823,FStar_Util.Inl t,uu____9825) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____9844,FStar_Util.Inr c,uu____9846) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          (FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u)))
            None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____9876;
             FStar_Syntax_Syntax.pos = uu____9877;
             FStar_Syntax_Syntax.vars = uu____9878;_},us)
          ->
          let uu____9884 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____9884 with
           | ((us',t),uu____9897) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____9905 =
                     let uu____9906 =
                       let uu____9909 = FStar_TypeChecker_Env.get_range env in
                       ("Unexpected number of universe instantiations",
                         uu____9909) in
                     FStar_Errors.Error uu____9906 in
                   Prims.raise uu____9905)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Unionfind.change u'' (Some u)
                         | uu____9917 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____9918 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____9926) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____9943 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____9943 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____9954  ->
                      match uu____9954 with
                      | (b,uu____9958) ->
                          let uu____9959 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____9959) bs1 in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1 in
                 let uu____9964 = universe_of_aux env res in
                 level_of_type env res uu____9964 in
               let u_c =
                 let uu____9966 =
                   FStar_TypeChecker_Env.effect_repr env c1 u_res in
                 match uu____9966 with
                 | None  -> u_res
                 | Some trepr ->
                     let uu____9969 = universe_of_aux env trepr in
                     level_of_type env trepr uu____9969 in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us)) in
               (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)) None
                 e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rec type_of_head retry hd2 args1 =
            let hd3 = FStar_Syntax_Subst.compress hd2 in
            match hd3.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown 
              |FStar_Syntax_Syntax.Tm_bvar _|FStar_Syntax_Syntax.Tm_delayed _
                -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar _
              |FStar_Syntax_Syntax.Tm_name _
               |FStar_Syntax_Syntax.Tm_uvar _
                |FStar_Syntax_Syntax.Tm_uinst _
                 |FStar_Syntax_Syntax.Tm_ascribed _
                  |FStar_Syntax_Syntax.Tm_refine _
                   |FStar_Syntax_Syntax.Tm_constant _
                    |FStar_Syntax_Syntax.Tm_arrow _
                     |FStar_Syntax_Syntax.Tm_meta _
                      |FStar_Syntax_Syntax.Tm_type _
                ->
                let uu____10055 = universe_of_aux env hd3 in
                (uu____10055, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____10065,hd4::uu____10067) ->
                let uu____10114 = FStar_Syntax_Subst.open_branch hd4 in
                (match uu____10114 with
                 | (uu____10124,uu____10125,hd5) ->
                     let uu____10141 = FStar_Syntax_Util.head_and_args hd5 in
                     (match uu____10141 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____10176 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.NoDeltaSteps] env e in
                let uu____10178 = FStar_Syntax_Util.head_and_args e1 in
                (match uu____10178 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____10213 ->
                let uu____10214 =
                  FStar_TypeChecker_Env.clear_expected_typ env in
                (match uu____10214 with
                 | (env1,uu____10228) ->
                     let env2 =
                       let uu___131_10232 = env1 in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___131_10232.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___131_10232.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___131_10232.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___131_10232.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___131_10232.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___131_10232.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___131_10232.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___131_10232.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___131_10232.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___131_10232.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___131_10232.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___131_10232.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___131_10232.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___131_10232.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___131_10232.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___131_10232.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___131_10232.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___131_10232.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___131_10232.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___131_10232.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___131_10232.FStar_TypeChecker_Env.qname_and_index)
                       } in
                     ((let uu____10234 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf") in
                       if uu____10234
                       then
                         let uu____10235 =
                           let uu____10236 =
                             FStar_TypeChecker_Env.get_range env2 in
                           FStar_Range.string_of_range uu____10236 in
                         let uu____10237 =
                           FStar_Syntax_Print.term_to_string hd3 in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____10235 uu____10237
                       else ());
                      (let uu____10239 = tc_term env2 hd3 in
                       match uu____10239 with
                       | (uu____10252,{
                                        FStar_Syntax_Syntax.eff_name =
                                          uu____10253;
                                        FStar_Syntax_Syntax.res_typ = t;
                                        FStar_Syntax_Syntax.cflags =
                                          uu____10255;
                                        FStar_Syntax_Syntax.comp =
                                          uu____10256;_},g)
                           ->
                           ((let uu____10266 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____10266 Prims.ignore);
                            (t, args1))))) in
          let uu____10274 = type_of_head true hd1 args in
          (match uu____10274 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env t in
               let uu____10303 = FStar_Syntax_Util.arrow_formals_comp t1 in
               (match uu____10303 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1 in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____10336 =
                         FStar_Syntax_Print.term_to_string res1 in
                       level_of_type_fail env e uu____10336)))
      | FStar_Syntax_Syntax.Tm_match (uu____10339,hd1::uu____10341) ->
          let uu____10388 = FStar_Syntax_Subst.open_branch hd1 in
          (match uu____10388 with
           | (uu____10391,uu____10392,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____10408,[]) ->
          level_of_type_fail env e "empty match cases"
let universe_of:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun e  ->
      let uu____10442 = universe_of_aux env e in
      level_of_type env e uu____10442
let tc_tparams:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders* FStar_TypeChecker_Env.env*
        FStar_Syntax_Syntax.universes)
  =
  fun env  ->
    fun tps  ->
      let uu____10455 = tc_binders env tps in
      match uu____10455 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))